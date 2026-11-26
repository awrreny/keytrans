use super::tree_math::{
    Hash, hash_content_from_hash, is_retained_node, node_contains_retained, node_mid_from_range,
    parent_hash_from_hash_contents,
};

#[derive(Debug)]
pub enum VerifyError {
    RootMismatch {},
    ProofTooShort {},
    ProofTooLong {},
    RetainedTooShort {},
    RetainedTooLong {},
    RetainedMismatch {},
    TargetsNotStrictlyIncreasing {},
}

pub fn verify_combined(
    proof: &[Hash],
    leaf_hash: Hash,
    leaf_index: usize,
    retained_size: usize,
    retained_hashes: &[Hash],
    tree_size: usize,
    expected_root: Hash,
) -> Result<(), VerifyError> {
    verify_combined_multi(
        proof,
        &[(leaf_index, leaf_hash)],
        retained_size,
        retained_hashes,
        tree_size,
        expected_root,
    )
}

pub fn verify_combined_multi(
    proof: &[Hash],
    targets: &[(usize, Hash)],
    retained_size: usize,
    retained_hashes: &[Hash],
    tree_size: usize,
    expected_root: Hash,
) -> Result<(), VerifyError> {
    if !targets.windows(2).all(|w| w[0].0 < w[1].0) {
        return Err(VerifyError::TargetsNotStrictlyIncreasing {});
    }

    let mut proof = proof.iter();
    let mut retained_hashes = retained_hashes.iter();

    let computed_root = verify_combined_aux(
        &mut proof,
        targets,
        retained_size,
        &mut retained_hashes,
        0,
        tree_size,
    )?;

    if proof.next().is_some() {
        return Err(VerifyError::ProofTooLong {});
    }

    if retained_hashes.next().is_some() {
        return Err(VerifyError::RetainedTooLong {});
    }

    if computed_root == expected_root {
        Ok(())
    } else {
        Err(VerifyError::RootMismatch {})
    }
}

fn verify_combined_aux<'a>(
    proof: &mut impl Iterator<Item = &'a Hash>,
    targets: &[(usize, Hash)],
    retained_size: usize,
    retained_hashes: &mut impl Iterator<Item = &'a Hash>,
    left: usize,
    right: usize,
) -> Result<Hash, VerifyError> {
    let node_size = right - left;
    let node_contains_target = !targets.is_empty();

    let mut retained_expected = None;
    if is_retained_node(retained_size, left, right) {
        // If we don't stop recursion here, we still need to check that when we derive the hash for this node, this matches the retained hash.
        match retained_hashes.next() {
            None => return Err(VerifyError::RetainedTooShort {}),
            Some(h) => {
                if !node_contains_target {
                    return Ok(*h);
                }
                retained_expected = Some(*h)
            }
        }
    }

    if node_contains_target && node_size == 1 {
        debug_assert!(targets.len() == 1);
        let (_, leaf_hash) = targets[0];
        verify_retained(retained_expected, leaf_hash)?;
        return Ok(leaf_hash);
    }

    if node_size.is_power_of_two()
        && !node_contains_retained(retained_size, left, right)
        && !node_contains_target
    {
        return match proof.next() {
            None => Err(VerifyError::ProofTooShort {}),
            Some(h) => Ok(*h),
        };
    }

    // guaranteed to not be leaf because of previous check
    let mid = node_mid_from_range(left, right);
    let split = targets.partition_point(|&(i, _)| i < mid);

    let left_hash = verify_combined_aux(
        proof,
        &targets[..split],
        retained_size,
        retained_hashes,
        left,
        mid,
    )?;
    let left_hash_content = hash_content_from_hash((mid - left) == 1, left_hash);

    let right_hash = verify_combined_aux(
        proof,
        &targets[split..],
        retained_size,
        retained_hashes,
        mid,
        right,
    )?;
    let right_hash_content = hash_content_from_hash((right - mid) == 1, right_hash);

    let node_hash = parent_hash_from_hash_contents(left_hash_content, right_hash_content);

    verify_retained(retained_expected, node_hash)?;

    Ok(node_hash)
}

fn verify_retained(retained_expected: Option<Hash>, node_hash: Hash) -> Result<(), VerifyError> {
    if let Some(h) = retained_expected
        && h != node_hash
    {
        return Err(VerifyError::RetainedMismatch {});
    };
    Ok(())
}

// Adapted from RFC 9162 Section 2.1.3.2
pub fn verify_inclusion(
    proof: &[Hash],
    leaf_hash: Hash,
    leaf_index: usize,
    tree_size: usize,
    expected_root: Hash,
) -> bool {
    if tree_size == 0 || leaf_index >= tree_size {
        return false;
    }

    let mut node_index = leaf_index;
    let mut last_index = tree_size - 1;
    let mut level: u32 = 0;
    let mut cur_hash_content = hash_content_from_hash(true, leaf_hash);

    for sibling_hash in proof {
        if last_index == 0 {
            return false;
        }

        // If the node is not on the same level as its sibling, treat it as if it is in a higher level
        if node_index == last_index && node_index.is_multiple_of(2) {
            while node_index.is_multiple_of(2) && node_index != 0 {
                node_index >>= 1;
                last_index >>= 1;
                level += 1;
            }
        }

        let is_last_left_child = node_index + 1 == last_index && node_index.is_multiple_of(2);

        // Each node at this level covers 2**level leaves, so if there is 1 more than a multiple of that, the last must be in its own block, i.e. a leaf.
        let sibling_is_leaf =
            level == 0 || (is_last_left_child && (tree_size - 1).is_multiple_of(1 << level));

        let sibling_hash_content = hash_content_from_hash(sibling_is_leaf, *sibling_hash);

        let parent_hash = if node_index % 2 == 1 {
            parent_hash_from_hash_contents(sibling_hash_content, cur_hash_content)
        } else {
            parent_hash_from_hash_contents(cur_hash_content, sibling_hash_content)
        };
        cur_hash_content = hash_content_from_hash(false, parent_hash);

        node_index >>= 1;
        last_index >>= 1;
        level += 1;
    }

    last_index == 0 && cur_hash_content[1..] == expected_root[..]
}

#[cfg(test)]
mod tests {
    use super::super::test_utils::{dummy_entry, naive_retained_heads, naive_root_hash};
    use super::super::tree::{LogTree, ProveError};
    use super::*;

    #[test]
    fn verify_inclusion_accepts_every_proof_up_to_twenty_leaves() {
        for n in 1..=20usize {
            let mut tree = LogTree::new(dummy_entry(1));
            let mut leaves = vec![dummy_entry(1).get_hash()];
            for timestamp in 2..=n {
                tree.append(dummy_entry(timestamp as u64));
                leaves.push(dummy_entry(timestamp as u64).get_hash());
            }
            let root = naive_root_hash(&leaves);

            for (i, &leaf) in leaves.iter().enumerate() {
                let proof = tree.prove(i).expect("index in range");
                assert!(
                    verify_inclusion(&proof, leaf, i, n, root),
                    "n = {n}, i = {i}"
                );
            }
        }
    }

    #[test]
    fn verify_inclusion_rejects_proof_checked_against_the_wrong_index() {
        let n = 7;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        for (i, &leaf) in leaves.iter().enumerate() {
            let proof = tree.prove(i).expect("index in range");
            for wrong_index in 0..n {
                assert_eq!(
                    verify_inclusion(&proof, leaf, wrong_index, n, root),
                    i == wrong_index,
                    "proof for leaf {i} checked against index {wrong_index}"
                );
            }
        }
    }

    #[test]
    fn verify_inclusion_rejects_tampered_or_truncated_proofs() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let mut tampered = tree.prove(4).expect("index in range");
        tampered[0][0] ^= 0x01;
        assert!(!verify_inclusion(&tampered, leaves[4], 4, n, root));

        let mut truncated = tree.prove(4).expect("index in range");
        truncated.pop();
        assert!(!verify_inclusion(&truncated, leaves[4], 4, n, root));
    }

    #[test]
    fn verify_combined_accepts_every_proof_up_to_twenty_leaves() {
        for n in 1..=20usize {
            let mut tree = LogTree::new(dummy_entry(1));
            let mut leaves = vec![dummy_entry(1).get_hash()];
            for timestamp in 2..=n {
                tree.append(dummy_entry(timestamp as u64));
                leaves.push(dummy_entry(timestamp as u64).get_hash());
            }
            let root = naive_root_hash(&leaves);

            for retained in 0..=n {
                let heads = naive_retained_heads(&leaves[..retained]);
                for (i, &leaf) in leaves.iter().enumerate() {
                    let proof = tree.prove_combined(i, retained).expect("index in range");
                    assert!(
                        verify_combined(&proof, leaf, i, retained, &heads, n, root).is_ok(),
                        "n = {n}, retained = {retained}, i = {i}"
                    );
                }
            }
        }
    }

    #[test]
    fn verify_combined_rejects_proof_checked_against_the_wrong_index() {
        let n = 7;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 4;
        let heads = naive_retained_heads(&leaves[..retained]);

        for (i, &leaf) in leaves.iter().enumerate() {
            let proof = tree.prove_combined(i, retained).expect("index in range");
            for wrong_index in 0..n {
                assert_eq!(
                    verify_combined(&proof, leaf, wrong_index, retained, &heads, n, root).is_ok(),
                    i == wrong_index,
                    "proof for leaf {i} checked against index {wrong_index}"
                );
            }
        }

        let proof = tree.prove_combined(0, retained).expect("index in range");
        for out_of_range in [n, n + 1, usize::MAX] {
            assert!(
                verify_combined(&proof, leaves[0], out_of_range, retained, &heads, n, root)
                    .is_err(),
                "out of range index {out_of_range}"
            );
        }
    }

    #[test]
    fn verify_combined_rejects_tampered_or_truncated_proofs() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 5;
        let heads = naive_retained_heads(&leaves[..retained]);

        let mut tampered = tree.prove_combined(4, retained).expect("index in range");
        tampered[0][0] ^= 0x01;
        assert!(verify_combined(&tampered, leaves[4], 4, retained, &heads, n, root).is_err());

        let mut truncated = tree.prove_combined(4, retained).expect("index in range");
        truncated.pop();
        assert!(verify_combined(&truncated, leaves[4], 4, retained, &heads, n, root).is_err());

        let mut wrong_retained_head = heads.clone();
        wrong_retained_head[0][0] ^= 0x01;
        assert!(
            verify_combined(
                &tree.prove_combined(4, retained).expect("index in range"),
                leaves[4],
                4,
                retained,
                &wrong_retained_head,
                n,
                root
            )
            .is_err()
        );
    }

    #[test]
    fn verify_combined_rejects_extended_proofs() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 5;
        let heads = naive_retained_heads(&leaves[..retained]);

        let mut extended = tree.prove_combined(4, retained).expect("index in range");
        extended.push([0xAB; 32]);
        assert!(verify_combined(&extended, leaves[4], 4, retained, &heads, n, root).is_err());
    }

    #[test]
    fn verify_combined_rejects_mismatched_retained_head_containing_the_target() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 5;
        let mut heads = naive_retained_heads(&leaves[..retained]);
        heads[1][0] ^= 0x01;

        let proof = tree.prove_combined(4, retained).expect("index in range");
        assert!(verify_combined(&proof, leaves[4], 4, retained, &heads, n, root).is_err());
    }

    #[test]
    fn verify_combined_multi_accepts_every_pair_of_leaves_up_to_twenty_leaves() {
        for n in 1..=20usize {
            let mut tree = LogTree::new(dummy_entry(1));
            let mut leaves = vec![dummy_entry(1).get_hash()];
            for timestamp in 2..=n {
                tree.append(dummy_entry(timestamp as u64));
                leaves.push(dummy_entry(timestamp as u64).get_hash());
            }
            let root = naive_root_hash(&leaves);

            for retained in 0..=n {
                let heads = naive_retained_heads(&leaves[..retained]);
                for i in 0..n {
                    for j in (i + 1)..n {
                        let proof = tree
                            .prove_combined_multi(&[i, j], retained)
                            .expect("in range");
                        assert!(
                            verify_combined_multi(
                                &proof,
                                &[(i, leaves[i]), (j, leaves[j])],
                                retained,
                                &heads,
                                n,
                                root
                            )
                            .is_ok(),
                            "n = {n}, retained = {retained}, targets = {i}, {j}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn verify_combined_multi_accepts_empty_targets_up_to_twenty_leaves() {
        for n in 1..=20usize {
            let mut tree = LogTree::new(dummy_entry(1));
            let mut leaves = vec![dummy_entry(1).get_hash()];
            for timestamp in 2..=n {
                tree.append(dummy_entry(timestamp as u64));
                leaves.push(dummy_entry(timestamp as u64).get_hash());
            }
            let root = naive_root_hash(&leaves);

            for retained in 0..=n {
                let heads = naive_retained_heads(&leaves[..retained]);
                let proof = tree.prove_combined_multi(&[], retained).expect("in range");
                assert!(
                    verify_combined_multi(&proof, &[], retained, &heads, n, root).is_ok(),
                    "n = {n}, retained = {retained}"
                );
            }
        }
    }

    #[test]
    fn combined_multi_rejects_unsorted_duplicate_and_out_of_range_targets() {
        let n = 5;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 2;
        let heads = naive_retained_heads(&leaves[..retained]);

        assert!(matches!(
            tree.prove_combined_multi(&[3, 1], retained),
            Err(ProveError::TargetsNotStrictlyIncreasing {})
        ));
        assert!(matches!(
            tree.prove_combined_multi(&[1, 1], retained),
            Err(ProveError::TargetsNotStrictlyIncreasing {})
        ));
        assert!(matches!(
            tree.prove_combined_multi(&[1, n], retained),
            Err(ProveError::IndexOutOfRange { index, tree_size }) if index == n && tree_size == n
        ));

        let proof = tree
            .prove_combined_multi(&[1, 3], retained)
            .expect("in range");
        assert!(matches!(
            verify_combined_multi(
                &proof,
                &[(3, leaves[3]), (1, leaves[1])],
                retained,
                &heads,
                n,
                root
            ),
            Err(VerifyError::TargetsNotStrictlyIncreasing {})
        ));
        assert!(matches!(
            verify_combined_multi(
                &proof,
                &[(1, leaves[1]), (1, leaves[3])],
                retained,
                &heads,
                n,
                root
            ),
            Err(VerifyError::TargetsNotStrictlyIncreasing {})
        ));
    }

    #[test]
    fn verify_combined_multi_rejects_tampered_truncated_or_extended_proofs() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        let retained = 5;
        let heads = naive_retained_heads(&leaves[..retained]);
        let targets = [(1, leaves[1]), (6, leaves[6])];

        let proof = tree
            .prove_combined_multi(&[1, 6], retained)
            .expect("in range");
        assert!(verify_combined_multi(&proof, &targets, retained, &heads, n, root).is_ok());

        assert!(
            verify_combined_multi(
                &proof,
                &[(1, leaves[1]), (7, leaves[7])],
                retained,
                &heads,
                n,
                root
            )
            .is_err()
        );

        let mut tampered = proof.clone();
        tampered[0][0] ^= 0x01;
        assert!(verify_combined_multi(&tampered, &targets, retained, &heads, n, root).is_err());

        let mut truncated = proof.clone();
        truncated.pop();
        assert!(verify_combined_multi(&truncated, &targets, retained, &heads, n, root).is_err());

        let mut extended = proof.clone();
        extended.push([0xAB; 32]);
        assert!(verify_combined_multi(&extended, &targets, retained, &heads, n, root).is_err());
    }

    #[test]
    fn verify_combined_multi_checks_retained_head_containing_both_targets() {
        let n = 9;
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];
        for timestamp in 2..=n {
            tree.append(dummy_entry(timestamp as u64));
            leaves.push(dummy_entry(timestamp as u64).get_hash());
        }
        let root = naive_root_hash(&leaves);

        // retained = 8 is a single size-8 head containing both targets
        let retained = 8;
        let heads = naive_retained_heads(&leaves[..retained]);
        let targets = [(2, leaves[2]), (6, leaves[6])];

        let proof = tree
            .prove_combined_multi(&[2, 6], retained)
            .expect("in range");
        assert!(verify_combined_multi(&proof, &targets, retained, &heads, n, root).is_ok());

        let mut wrong_retained_head = heads.clone();
        wrong_retained_head[0][0] ^= 0x01;
        assert!(
            verify_combined_multi(&proof, &targets, retained, &wrong_retained_head, n, root)
                .is_err()
        );
    }
}
