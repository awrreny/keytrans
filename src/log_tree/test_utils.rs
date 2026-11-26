use sha2::{Digest, Sha256};

use super::tree::LogEntry;
use super::tree_math::Hash;

pub(super) fn dummy_entry(timestamp: u64) -> LogEntry {
    LogEntry::new(timestamp, [timestamp as u8; 32])
}

pub(super) fn naive_root_hash(leaves: &[Hash]) -> Hash {
    if leaves.len() == 1 {
        return leaves[0];
    }

    let mid = 1 << (leaves.len() - 1).ilog2();
    let left_hash = naive_root_hash(&leaves[..mid]);
    let right_hash = naive_root_hash(&leaves[mid..]);

    let mut h = Sha256::new();
    h.update([tag(mid)]);
    h.update(left_hash);
    h.update([tag(leaves.len() - mid)]);
    h.update(right_hash);
    h.finalize().into()
}

fn tag(len: usize) -> u8 {
    if len == 1 { 0x00 } else { 0x01 }
}

fn get_subtrees_as_ranges_aux(out: &mut Vec<(usize, usize)>, left: usize, right: usize) {
    out.push((left, right));
    if right - left <= 1 {
        return;
    }
    let mid = left + (1 << (right - left - 1).ilog2());
    get_subtrees_as_ranges_aux(out, left, mid);
    get_subtrees_as_ranges_aux(out, mid, right);
}

pub(super) fn get_subtrees_as_ranges(leaf_count: usize) -> Vec<(usize, usize)> {
    let mut out = vec![];
    get_subtrees_as_ranges_aux(&mut out, 0, leaf_count);
    out
}

pub(super) fn naive_retained_heads(leaves: &[Hash]) -> Vec<Hash> {
    let mut heads = vec![];
    let mut left = 0;
    let mut remaining = leaves.len();
    while remaining > 0 {
        let size = 1 << remaining.ilog2();
        heads.push(naive_root_hash(&leaves[left..left + size]));
        left += size;
        remaining -= size;
    }
    heads
}
