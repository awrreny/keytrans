use sha2::{Digest, Sha256};

type Hash = [u8; 32];
type HashContent = [u8; 33];

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
    fn get_hash(&self) -> Hash {
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

    // Specified in 11.8
    // https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-06.html#name-log-tree-2
    fn hash_content(&self) -> HashContent {
        let mut out = [0u8; 33];
        out[0] = if self.is_leaf() { 0x00 } else { 0x01 };
        out[1..].copy_from_slice(&self.hash);
        out
    }

    fn parent_hash_from_hash_contents(
        left_content: HashContent,
        right_content: HashContent,
    ) -> Hash {
        let mut h = Sha256::new();
        h.update(left_content);
        h.update(right_content);
        h.finalize().into()
    }

    fn parent_hash_from_nodes(left: &Node, right: &Node) -> Hash {
        Node::parent_hash_from_hash_contents(left.hash_content(), right.hash_content())
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
            let new_hash = Node::parent_hash_from_hash_contents(node.hash_content(), accumulator);
            accumulator[0] = 0x01; // guaranteed to be a parent
            accumulator[1..].copy_from_slice(&new_hash);
        }

        accumulator[1..]
            .try_into()
            .expect("Accumulator is the wrong length")
    }

    pub fn prove(&self, leaf_index: usize) -> Vec<Hash> {
        self.prove_aux(leaf_index, 0, self.size())
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
        let largest_power_of_two_less_than = 1 << (right - left - 1).ilog2();
        let mid = left + largest_power_of_two_less_than;

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
                let new_hash =
                    Node::parent_hash_from_hash_contents(node.hash_content(), accumulator);
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
    use super::*;

    fn dummy_entry(timestamp: u64) -> LogEntry {
        LogEntry {
            timestamp,
            prefix_root: [timestamp as u8; 32],
        }
    }

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
}
