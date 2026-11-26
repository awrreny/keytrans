use sha2::{Digest, Sha256};

pub(super) type Hash = [u8; 32];
pub(super) type HashContent = [u8; 33];

pub(super) fn is_retained_node(retained_size: usize, left: usize, right: usize) -> bool {
    let node_size = right - left;

    // sizes of retained trees is binary decomposition of retained_leaves
    // node is a complete subtree
    // && there is a retained head with the same size of the node
    // && if you get rid of smaller retained heads, 'right' coincides with the remaining size of the retained heads
    node_size.is_power_of_two()
        && node_size & retained_size != 0
        && right == (retained_size & !(node_size - 1))
}

pub(super) fn node_contains_retained(retained_size: usize, left: usize, right: usize) -> bool {
    left < retained_size && (right > retained_size || !(right - left).is_power_of_two())
}

pub(super) fn node_mid_from_range(left: usize, right: usize) -> usize {
    let largest_power_of_two_less_than = 1 << (right - left - 1).ilog2();
    left + largest_power_of_two_less_than
}

pub(super) fn hash_content_from_hash(is_leaf: bool, hash: Hash) -> HashContent {
    let mut out = [0u8; 33];
    out[0] = if is_leaf { 0x00 } else { 0x01 };
    out[1..].copy_from_slice(&hash);
    out
}

pub(super) fn parent_hash_from_hash_contents(
    left_content: HashContent,
    right_content: HashContent,
) -> Hash {
    let mut h = Sha256::new();
    h.update(left_content);
    h.update(right_content);
    h.finalize().into()
}
