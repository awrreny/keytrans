use sha2::{Digest, Sha256};

use super::tree_math::{
    Hash, HashContent, hash_content_from_hash, is_retained_node, node_contains_retained,
    node_mid_from_range, parent_hash_from_hash_contents,
};

#[derive(Debug)]
pub enum ProveError {
    IndexOutOfRange { index: usize, tree_size: usize },
    TargetsNotStrictlyIncreasing {},
}

pub struct LogEntry {
    timestamp: u64,
    prefix_root: Hash,
}

impl LogEntry {
    pub fn new(timestamp: u64, prefix_root: Hash) -> LogEntry {
        LogEntry {
            timestamp,
            prefix_root,
        }
    }

    // Specified in 11.8
    // https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-06.html#name-log-tree-2
    pub(crate) fn get_hash(&self) -> Hash {
        let mut h = Sha256::new();
        h.update(self.timestamp.to_be_bytes());
        h.update(self.prefix_root);
        h.finalize().into()
    }
}

// All non-leaf nodes will have both left and right children
struct Node {
    hash: Hash,
    leaf_count: u64,
    children: Option<(Box<Node>, Box<Node>)>,
}

impl Node {
    fn new(entry: &LogEntry) -> Node {
        Node {
            hash: entry.get_hash(),
            leaf_count: 1,
            children: None,
        }
    }

    fn is_leaf(&self) -> bool {
        self.children.is_none()
    }

    fn hash_content(&self) -> HashContent {
        hash_content_from_hash(self.is_leaf(), self.hash)
    }

    fn parent_hash_from_nodes(left: &Node, right: &Node) -> Hash {
        parent_hash_from_hash_contents(left.hash_content(), right.hash_content())
    }

    fn parent(left: Node, right: Node) -> Node {
        Node {
            hash: Node::parent_hash_from_nodes(&left, &right),
            leaf_count: left.leaf_count + right.leaf_count,
            children: Some((Box::new(left), Box::new(right))),
        }
    }
}

pub struct LogTree {
    complete_blocks: Vec<Node>,
    log_entries: Vec<LogEntry>,
}

impl LogTree {
    // Empty log tree is not defined by the draft
    pub fn new(entry: LogEntry) -> LogTree {
        LogTree {
            complete_blocks: vec![Node::new(&entry)],
            log_entries: vec![entry],
        }
    }

    pub fn size(&self) -> usize {
        self.log_entries.len()
    }

    pub fn append(&mut self, entry: LogEntry) {
        let mut node = Node::new(&entry);

        while let Some(block) = self
            .complete_blocks
            .pop_if(|last| last.leaf_count == node.leaf_count)
        {
            node = Node::parent(block, node)
        }

        self.complete_blocks.push(node);
        self.log_entries.push(entry);
    }

    pub fn root(&self) -> Hash {
        let mut accumulator = self
            .complete_blocks
            .last()
            .expect("Complete block list should never be empty")
            .hash_content();

        for node in self.complete_blocks.iter().rev().skip(1) {
            let new_hash = parent_hash_from_hash_contents(node.hash_content(), accumulator);
            accumulator[0] = 0x01; // guaranteed to be a parent
            accumulator[1..].copy_from_slice(&new_hash);
        }

        accumulator[1..]
            .try_into()
            .expect("Accumulator is the wrong length")
    }

    pub fn prove_combined(
        &self,
        leaf_index: usize,
        retained_leaves: usize,
    ) -> Result<Vec<Hash>, ProveError> {
        self.prove_combined_multi(&[leaf_index], retained_leaves)
    }

    // Invariant: `targets` is strictly increasing and every index is in [left, right)
    fn prove_combined_aux(
        &self,
        targets: &[usize],
        retained_size: usize,
        left: usize,
        right: usize,
        proof: &mut Vec<Hash>,
    ) {
        let node_size = right - left;
        let node_contains_target = !targets.is_empty();
        // target leaf: continue
        // retained and target is not inside: continue
        // node complete and doesn't contain anything retained or target: add to proof, continue
        // otherwise recurse (error if leaf, actually leaf case is completely covered)

        // Leaf to be proved is not in the proof
        if node_contains_target && node_size == 1 {
            return;
        }

        let is_retained_node = is_retained_node(retained_size, left, right);
        if !node_contains_target && is_retained_node {
            return;
        }

        let node_contains_retained = node_contains_retained(retained_size, left, right);

        if node_size.is_power_of_two() && !node_contains_retained && !node_contains_target {
            proof.push(self.hash_of_range(left, right));
            return;
        }

        let mid = node_mid_from_range(left, right);
        let split = targets.partition_point(|&i| i < mid);

        self.prove_combined_aux(&targets[..split], retained_size, left, mid, proof);
        self.prove_combined_aux(&targets[split..], retained_size, mid, right, proof);
    }

    // Prove the inclusion of multiple (or 0) leaves
    pub fn prove_combined_multi(
        &self,
        targets: &[usize],
        retained_leaves: usize,
    ) -> Result<Vec<Hash>, ProveError> {
        for &index in targets {
            if index >= self.size() {
                return Err(ProveError::IndexOutOfRange {
                    index,
                    tree_size: self.size(),
                });
            }
        }

        if !targets.windows(2).all(|w| w[0] < w[1]) {
            return Err(ProveError::TargetsNotStrictlyIncreasing {});
        }

        let mut proof = vec![];
        self.prove_combined_aux(targets, retained_leaves, 0, self.size(), &mut proof);
        Ok(proof)
    }

    pub fn prove(&self, leaf_index: usize) -> Result<Vec<Hash>, ProveError> {
        if leaf_index >= self.size() {
            return Err(ProveError::IndexOutOfRange {
                index: leaf_index,
                tree_size: self.size(),
            });
        }
        Ok(self.prove_aux(leaf_index, 0, self.size()))
    }

    // Gives a proof of leaf i's inclusion, by giving the hashes of the copath
    // left and right refer to which leaves are in the subtree currently being proved (used because we dont explicitly store the tree)
    fn prove_aux(&self, i: usize, left: usize, right: usize) -> Vec<Hash> {
        // leaf
        if right - left == 1 {
            return vec![];
        }

        // split range into left and right subtree
        // left subtree contains leaves in range [left, mid) and right has [mid, right)
        let mid = node_mid_from_range(left, right);

        if i < mid {
            let mut proof = self.prove_aux(i, left, mid);
            proof.push(self.hash_of_range(mid, right));
            proof
        } else {
            let mut proof = self.prove_aux(i, mid, right);
            proof.push(self.hash_of_range(left, mid));
            proof
        }
    }

    // Hash of the subtree covering leaves [left, right).
    // Assumes the range is a real subtree of the current tree (guaranteed by prove_aux)
    fn hash_of_range(&self, left: usize, right: usize) -> Hash {
        let length = (right - left) as u64;

        // If the subtree doesn't have a power-of-two amount of nodes then it is one of the rightmost non-complete subtrees, and has to be rederived
        if !length.is_power_of_two() {
            // Should be true if the tree is left-balanced
            debug_assert_eq!(right, self.log_entries.len());

            let last = self
                .complete_blocks
                .last()
                .expect("Complete block list should never be empty");
            let mut accumulator = last.hash_content();
            let mut leaf_count = last.leaf_count;

            for node in self.complete_blocks.iter().rev().skip(1) {
                let new_hash = parent_hash_from_hash_contents(node.hash_content(), accumulator);
                accumulator[0] = 0x01; // guaranteed to be a parent
                accumulator[1..].copy_from_slice(&new_hash);

                leaf_count += node.leaf_count;
                if leaf_count == length {
                    return new_hash;
                }
            }
            panic!("Range does not correspond to a valid subtree");
        }

        // Otherwise the subtree we are looking for is perfectly balanced
        let mut block_left = 0usize;
        for block in &self.complete_blocks {
            let block_right = block_left + block.leaf_count as usize;

            if left >= block_left && right <= block_right {
                let mut node = block;
                let (mut node_left, mut node_right) = (block_left, block_right);

                while (node_left, node_right) != (left, right) {
                    let (l, r) = node
                        .children
                        .as_ref()
                        .expect("Range should match a node in this block");
                    let mid = node_left + l.leaf_count as usize;

                    if right <= mid {
                        node = l;
                        node_right = mid;
                    } else {
                        debug_assert!(left >= mid);
                        node = r;
                        node_left = mid;
                    }
                }
                return node.hash;
            }
            block_left = block_right;
        }
        panic!("Range is not within the tree");
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_utils::{dummy_entry, get_subtrees_as_ranges, naive_root_hash};
    use super::*;

    #[test]
    fn five_leaf_tree_splits_into_four_and_one_leaf_blocks() {
        let mut tree = LogTree::new(dummy_entry(1));
        tree.append(dummy_entry(2));
        tree.append(dummy_entry(3));
        tree.append(dummy_entry(4));
        tree.append(dummy_entry(5));

        assert_eq!(tree.log_entries.len(), 5);
        assert_eq!(tree.complete_blocks.len(), 2);

        let block = &tree.complete_blocks[0];
        assert_eq!(block.leaf_count, 4);
        let (left, right) = block.children.as_ref().expect("four-leaf block");
        assert_eq!(left.leaf_count, 2);
        assert_eq!(right.leaf_count, 2);
        assert!(left.children.is_some());
        assert!(right.children.is_some());

        assert_eq!(tree.complete_blocks[1].leaf_count, 1);
        assert!(tree.complete_blocks[1].children.is_none());
    }
    #[test]
    fn two_leaf_tree_root() {
        let mut tree = LogTree::new(dummy_entry(1));
        tree.append(dummy_entry(2));

        assert_eq!(tree.complete_blocks.len(), 1);
        let block = &tree.complete_blocks[0];
        assert_eq!(block.leaf_count, 2);

        let mut left_hasher = Sha256::new();
        left_hasher.update(1u64.to_be_bytes());
        left_hasher.update([1u8; 32]);
        let left_leaf_hash: Hash = left_hasher.finalize().into();

        let mut right_hasher = Sha256::new();
        right_hasher.update(2u64.to_be_bytes());
        right_hasher.update([2u8; 32]);
        let right_leaf_hash: Hash = right_hasher.finalize().into();

        let mut expected = Sha256::new();
        expected.update([0x00]);
        expected.update(left_leaf_hash);
        expected.update([0x00]);
        expected.update(right_leaf_hash);

        let expected_root: Hash = expected.finalize().into();
        assert_eq!(tree.root(), expected_root);
    }

    #[test]
    fn hash_of_range_returns_complete_block_hash() {
        let mut tree = LogTree::new(dummy_entry(1));
        for timestamp in 2..=4 {
            tree.append(dummy_entry(timestamp));
        }

        assert_eq!(tree.hash_of_range(0, 4), tree.complete_blocks[0].hash);
    }

    #[test]
    fn root_hash_matches_naive_implementation() {
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];

        for timestamp in 2..=64 {
            tree.append(dummy_entry(timestamp));
            leaves.push(dummy_entry(timestamp).get_hash());

            assert_eq!(
                tree.root(),
                naive_root_hash(&leaves),
                "tree size {timestamp}"
            );
        }
    }

    #[test]
    fn hash_of_range_matches_naive_implementation() {
        let mut tree = LogTree::new(dummy_entry(1));
        let mut leaves = vec![dummy_entry(1).get_hash()];

        for timestamp in 2..=48 {
            tree.append(dummy_entry(timestamp));
            leaves.push(dummy_entry(timestamp).get_hash());

            for (left, right) in get_subtrees_as_ranges(leaves.len()) {
                assert_eq!(
                    tree.hash_of_range(left, right),
                    naive_root_hash(&leaves[left..right]),
                    "tree size {timestamp} from {left} to {right}"
                );
            }
        }
    }
}
