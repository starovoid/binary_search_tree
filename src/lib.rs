#![allow(dead_code)]
use std::mem;
use std::cmp::Ordering;

/// A simple binary search tree
/// 
/// # Examples
/// 
/// ```
/// use binary_search_tree::BinarySearchTree;
/// 
/// // Creating a BST that will contain i32 integers
/// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
/// 
/// // Adding the following elements to the tree
/// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
/// tree.insert(18); tree.insert(45); tree.insert(35);
/// 
/// // Inorder traversal: tree elements in sorted order
/// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
/// 
/// // Min and max values:
/// assert_eq!(tree.min().unwrap(), &10);
/// assert_eq!(tree.max().unwrap(), &45);
/// 
/// // Contains
/// assert!(tree.contains(&15));
/// assert!(!tree.contains(&99));
/// 
/// // Removal
/// tree.remove(&35);
/// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &40, &45]);
/// ```
/// 
/// For more examples, see the methods documentation in the impl block


#[derive(Debug)]
pub struct BinarySearchTree<T: Ord> {
    root: Link<T>,
    pub size: usize,
}

#[derive(Debug)]
struct Node<T: Ord> {
    value: T,
    left: Link<T>,
    right: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;


impl<T: Ord> BinarySearchTree<T> {
    /// Makes a new empty BST.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// // New bst that will be contains i32
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// ```
    pub fn new() -> Self {
        BinarySearchTree { root: None, size: 0 }
    }
    
    /// Сhecking if the tree is empty
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    
    /// Clears the inary search tree, removing all elements.
    ///
    /// # Examples
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    ///
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(1);
    /// tree.clear();
    /// assert!(tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        *self = BinarySearchTree::new();
    }

    /// Viewing the root element of the tree
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.root().is_none(), true);  // is empty
    /// 
    /// tree.insert(1); tree.insert(0); tree.insert(2);
    /// 
    /// // the first element inserted becomes the root
    /// assert_eq!(tree.root().unwrap(), &1);
    /// ```
    pub fn root(&self) -> Option<&T> {
        self.root.as_ref().map(|node| &node.value)
    }
    
    /// Inserting a new element in the tree
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(1); tree.insert(0); tree.insert(2); tree.insert(1);
    /// assert_eq!(tree.size, 4);
    /// 
    /// // Elements in sorted order (inorder traversal)
    /// assert_eq!(tree.sorted_vec(), vec![&0, &1, &1, &2]);
    /// ```
    pub fn insert(&mut self, value: T) {
        let new_node = Box::new(Node {
            value: value,
            left: None,
            right: None,
        });

        self.size += 1;
        
        if self.root.is_none() {
            self.root = Some(new_node);
        } else {
            let mut current = self.root.as_mut().unwrap();
            loop {
                if new_node.value < current.value {
                    match &current.left {
                        Some(_) => current = current.left.as_mut().unwrap(),
                        None => {
                            current.left = Some(new_node);
                            break;
                        },
                    };
                } else {
                    match &current.right {
                        Some(_) => current = current.right.as_mut().unwrap(),
                        None => {
                            current.right = Some(new_node);
                            break;
                        },
                    };
                }
            }
        }
    }
    
    /// Checks whether the tree contains an element with the specified value
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.contains(&1), false);
    /// 
    /// tree.insert(1); tree.insert(0); tree.insert(2); tree.insert(1);
    /// 
    /// // The contains() method accepts a reference to a value
    /// assert_eq!(tree.contains(&2), true);
    /// assert_eq!(tree.contains(&1), true);
    /// assert_eq!(tree.contains(&999), false);
    /// ```
    pub fn contains(&self, target: &T) -> bool {
        let mut current = self.root.as_ref();

        while let Some(node) = current {
            match node.value.cmp(target) {
                Ordering::Less => current = node.right.as_ref(),
                Ordering::Greater => current = node.left.as_ref(),
                Ordering::Equal => return true,
            }
        }
        false
    }
    
    /// The minimum element of the tree
    /// 
    /// Returns a reference to the minimum element.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.min(), None);
    /// 
    /// tree.insert(1); tree.insert(0); tree.insert(2); tree.insert(1);
    /// assert_eq!(tree.min().unwrap(), &0);
    /// ```
    pub fn min(&self) -> Option<&T> {
        // To find the maximum element, we will simply follow the right branches to the end
        if self.root.is_some() {
            let mut current = self.root.as_ref();
            while current.unwrap().left.is_some() {
                current = current.unwrap().left.as_ref();
            }
            current.map(|node| &node.value)
        } else {
            None
        }
    }
    
    /// The maximum element of the tree
    /// 
    /// Returns a reference to the maximum element.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.max(), None);
    /// 
    /// tree.insert(1); tree.insert(0); tree.insert(2); tree.insert(1);
    /// assert_eq!(tree.max().unwrap(), &2);
    /// ```
    pub fn max(&self) -> Option<&T> {
        // To find the maximum element, we will simply follow the right branches to the end
        if self.root.is_some() {
            let mut current = self.root.as_ref();
            while current.unwrap().right.is_some() {
                current = current.unwrap().right.as_ref();
            }
            current.map(|node| &node.value)
        } else {
            None
        }
    }
    
    /// Inorder successor of the element with the specified value
    /// 
    /// In Binary Search Tree, inorder successor of an input node can be defined as 
    /// the node with the smallest value greater than the value of the input node.
    /// In another way, we can say that the successor of element x is the element 
    /// immediately following it in sorted order.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// tree.insert(18); tree.insert(45); tree.insert(35);
    /// 
    /// // We have a binary tree with the following structure:
    /// //       25
    /// //   15      40
    /// // 10  18  35  45
    /// 
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
    /// 
    /// // and successor of 25 will be element 35.
    /// assert_eq!(tree.successor(&25).unwrap(), &35);
    /// 
    /// assert_eq!(tree.successor(&40).unwrap(), &45);
    /// assert!(tree.successor(&45).is_none()); // Element 45 has no successors
    /// 
    /// // We can also find successors for missing values in the tree
    /// assert_eq!(tree.successor(&20).unwrap(), &25); // [..., &18, vv&20vv, &25, ...]
    /// ```
    pub fn successor(&self, val: &T) -> Option<&T> {
        let mut current = self.root.as_ref();
        let mut successor = None;

        while current.is_some() {
            let node = current.unwrap();
            if node.value > *val {
                successor = current;
                current = node.left.as_ref();
            } else {
                current = node.right.as_ref();
            }
        }

        successor.map(|node| &node.value)
    }
    
    /// Inorder predecessor of the element with the specified value
    /// 
    /// In Binary Search Tree, inorder predecessor of an input node can be defined as 
    /// the node with the greatest value smaller than the value of the input node.
    /// In another way, we can say that the predecessor of element x is the element 
    /// immediately preceding it in sorted order.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// tree.insert(18); tree.insert(45); tree.insert(35);
    /// 
    /// // We have a binary tree with the following structure:
    /// //       25
    /// //   15      40
    /// // 10  18  35  45
    /// 
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
    /// 
    /// // and predecessor of 25 will be element 35.
    /// assert_eq!(tree.predecessor(&25).unwrap(), &18);
    /// 
    /// assert_eq!(tree.predecessor(&40).unwrap(), &35);
    /// assert!(tree.predecessor(&10).is_none()); // Element 10 has no predecessors
    /// 
    /// // We can also find predecessors for missing values in the tree
    /// assert_eq!(tree.predecessor(&20).unwrap(), &18); // [..., &18, vv&20vv, &25, ...]
    /// ```
    pub fn predecessor(&self, val: &T) -> Option<&T> {
        let mut current = self.root.as_ref();
        let mut predecessor = None;

        while current.is_some() {
            let node = current.unwrap();
            if node.value < *val {
                predecessor = current;
                current = node.right.as_ref();
            } else {
                current = node.left.as_ref();
            }
        }

        predecessor.map(|node| &node.value)
    }
    
    /// Remove element with the target value
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// tree.insert(18); tree.insert(45); tree.insert(35); tree.insert(18);
    /// 
    /// tree.remove(&18);
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
    /// assert_eq!(tree.size, 7);
    /// 
    /// tree.remove(&25);
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &35, &40, &45]);
    /// assert_eq!(tree.size, 6);
    /// 
    /// // If you try to delete a value that is missing from the tree, nothing will change
    /// tree.remove(&99);
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &35, &40, &45]);
    /// assert_eq!(tree.size, 6);
    /// ```
    pub fn remove(&mut self, target: &T) {
        let mut remove_occurred = false;

        if let Some(root) = self.root.as_mut() {
            if root.remove(target, &mut remove_occurred) {
                self.root.take();
            }
        }

        if remove_occurred {
            self.size -= 1;
        }
    }
    
    /// Vector of references to elements in the tree in non-decreasing order
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// tree.insert(18); tree.insert(45); tree.insert(35); tree.insert(18);
    /// 
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &18, &25, &35, &40, &45]);
    /// ```
    pub fn sorted_vec(&self) -> Vec<&T> {
        if let Some(root) = self.root.as_ref() {
            root.sorted_vec()
        } else {
            Vec::new()
        }
    }
    
    /// Moving a tree to a sorted vector
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// 
    ///assert_eq!(tree.into_sorted_vec(), vec![10, 15, 25, 40]);
    /// ```
    pub fn into_sorted_vec(self) -> Vec<T> {
        if let Some(root) = self.root {
            root.into_sorted_vec()
        } else {
            Vec::new()
        }
    }
}


impl<T: Ord + Clone > Clone for BinarySearchTree<T> {
    fn clone(&self) -> BinarySearchTree<T> {
        let mut new_tree = BinarySearchTree::new();

        for elem in self.sorted_vec().iter() {
            new_tree.insert((*elem).clone());
        }

        new_tree
    }
}


/// Most operations are performed on nodes externally in BinarySearchTree 
/// methods, but Node takes care of recursive algorithms: 
/// remove (), sorted_vec(), into_sorted_vec().
impl<T: Ord> Node<T> {
    /// Vector of references to elements in the subtree in non-decreasing order
    pub fn sorted_vec(&self) -> Vec<&T> {
        let mut elements = Vec::new();

        if let Some(left) = self.left.as_ref() {
            elements.extend(left.sorted_vec());
        }
        elements.push(&self.value);
        if let Some(right) = self.right.as_ref() {
            elements.extend(right.sorted_vec());
        }

        elements
    }
    
    /// Moving a tree to a sorted vector
    pub fn into_sorted_vec(self) -> Vec<T> {
        let mut elements = Vec::new();

        if let Some(left) = self.left {
            elements.extend(left.into_sorted_vec());
        }
        elements.push(self.value);
        if let Some(right) = self.right {
            elements.extend(right.into_sorted_vec());
        }

        elements
    }
    

    pub fn remove(&mut self, target: &T, status: &mut bool) -> bool {
        // returns true if this node is being deleted
        match self.value.cmp(target) {
            Ordering::Greater => if let Some(left) = self.left.as_mut() {
                if left.remove(target, status) {
                    self.left.take();
                };
            },
            Ordering::Less => if let Some(right) = self.right.as_mut() {
                if right.remove(target, status) {
                    self.right.take();
                }
            },
            Ordering::Equal => {
                *status = true;  // The required element exists and will be deleted soon

                match (self.left.as_ref(), self.right.as_ref()) {
                    (None, None) => {
                        // The node that is being deleted has no children. 
                        // return true so that the parent node discards it.
                        return true;
                    },
                    (Some(_), None) => {
                        // The node being deleted has only a left child, so we just replace it
                        *self = *self.left.take().unwrap();
                    },
                    (None, Some(_)) => {
                        // the node being deleted has only a right child, so we just replace it
                        *self = *self.right.take().unwrap();
                    },
                    (Some(_), Some(_)) => {
                        // The most complex case is when a node has two children and 
                        // we can't replace the current node with one of them.

                        // Find the successor of the element being deleted, swap values, 
                        // and delete the successor node recursively.
                        let mut current = self.right.as_mut().unwrap();
                        let successor;
                        
                        // Base case: the right child is the successor
                        if current.left.is_none() {
                            successor = self.right.as_mut().unwrap();
                            mem::swap(&mut self.value, &mut successor.value); // Swapping values
                            // Recursively deleting the receiver node
                            if successor.remove(target, status) {
                                self.right.take();
                            }
                        
                        // The successor is the minimum element of the right subtree
                        } else { 
                            while current.left.as_mut().unwrap().left.is_some() {
                                current = current.left.as_mut().unwrap();
                            }
                            successor = current.left.as_mut().unwrap();

                            mem::swap(&mut self.value, &mut successor.value); // Swapping values
                            // Recursively deleting the receiver node
                            if current.remove(target, status) {
                                current.left.take();
                            }
                        }
                    }
                }
            }
        }
        false
    }
}


#[cfg(test)]
mod test {
    use super::BinarySearchTree;

    #[test]
    fn basics() {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();

        //Check empty bst behaves right
        assert_eq!(tree.root.is_none(), true);
        assert_eq!(tree.size, 0);
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.contains(&5), false);
        tree.remove(&99);

        // Populate bst
        tree.insert(1); tree.insert(0); tree.insert(-2); tree.insert(5);
        tree.insert(5); tree.insert(15); tree.insert(-5); tree.insert(1);
        assert_eq!(tree.size, 8);
        assert_eq!(tree.root().unwrap(), &1);

        // Checking the operation of min(), max()
        assert_eq!(tree.min().unwrap(), &-5);
        assert_eq!(tree.max().unwrap(), &15);

        // Checking the operation of contains
        assert_eq!(tree.contains(&-5), true);
        assert_eq!(tree.contains(&0), true);
        assert_eq!(tree.contains(&55), false);

        // Checking the tree structure
        assert_eq!(tree.sorted_vec(), vec![&-5, &-2, &0, &1, &1, &5, &5, &15]);
        
        tree.remove(&99);
        assert_eq!(tree.sorted_vec(), vec![&-5, &-2, &0, &1, &1, &5, &5, &15]);
        tree.remove(&-5);
        assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &1, &5, &5, &15]);
        tree.remove(&0);
        assert_eq!(tree.sorted_vec(), vec![&-2, &1, &1, &5, &5, &15]);
        tree.remove(&5);
        assert_eq!(tree.sorted_vec(), vec![&-2, &1, &1, &5, &15]);
        tree.remove(&15);
        assert_eq!(tree.sorted_vec(), vec![&-2, &1, &1, &5]);
        tree.remove(&1);
        assert_eq!(tree.sorted_vec(), vec![&-2, &1, &5]);
        tree.remove(&1);
        assert_eq!(tree.sorted_vec(), vec![&-2, &5]);
        tree.remove(&-2);
        assert_eq!(tree.sorted_vec(), vec![&5]);
        tree.remove(&5);
        assert!(tree.is_empty());
        assert_eq!(tree.size, 0);
    }
    
    #[test]
    fn successor_and_predecessor() {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        assert!(tree.successor(&1).is_none());
        assert!(tree.predecessor(&1).is_none());

        tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
        tree.insert(18); tree.insert(45); tree.insert(35);
        
        // Testing successor
        assert_eq!(tree.successor(&25).unwrap(), &35);
        assert_eq!(tree.successor(&18).unwrap(), &25);
        assert_eq!(tree.successor(&40).unwrap(), &45);
        assert_eq!(tree.successor(&10).unwrap(), &15);
        assert!(tree.successor(&45).is_none());

        // Let's make sure that nothing has been violated
        assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
        
        // Testing predecessor
        assert_eq!(tree.predecessor(&25).unwrap(), &18);
        assert_eq!(tree.predecessor(&18).unwrap(), &15);
        assert_eq!(tree.predecessor(&40).unwrap(), &35);
        assert_eq!(tree.predecessor(&15).unwrap(), &10);
        assert!(tree.predecessor(&10).is_none());

        // Add duplicates
        tree.insert(10); tree.insert(25); tree.insert(35); tree.insert(45);

        // Testing successor
        assert_eq!(tree.successor(&25).unwrap(), &35);
        assert_eq!(tree.successor(&18).unwrap(), &25);
        assert_eq!(tree.successor(&40).unwrap(), &45);
        assert_eq!(tree.successor(&10).unwrap(), &15);
        assert!(tree.successor(&45).is_none());

        // Testing predecessor
        assert_eq!(tree.predecessor(&25).unwrap(), &18);
        assert_eq!(tree.predecessor(&18).unwrap(), &15);
        assert_eq!(tree.predecessor(&40).unwrap(), &35);
        assert_eq!(tree.predecessor(&15).unwrap(), &10);
        assert!(tree.predecessor(&10).is_none());

        // Let's make sure that nothing has been violated
        assert_eq!(tree.sorted_vec(), vec![&10, &10, &15, &18, &25, &25, &35, &35, &40, &45, &45]);
    }
    
    #[test]
    fn into_sorted_vec() {
        let tree: BinarySearchTree<i32> = BinarySearchTree::new();
        assert_eq!(tree.into_sorted_vec(), Vec::new());

        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
        tree.insert(18); tree.insert(45); tree.insert(35); tree.insert(18);

        assert_eq!(tree.into_sorted_vec(), vec![10, 15, 18, 18, 25, 35, 40, 45]);
    }

    #[test]
    fn clone() {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        tree.insert(1); tree.insert(0); tree.insert(-2); tree.insert(5);

        let mut cloned = tree.clone();
        cloned.insert(99); cloned.remove(&0);

        assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &5]);
        assert_eq!(cloned.sorted_vec(), vec![&-2, &1, &5, &99]);
    }

    #[test]
    fn with_string() {
        let mut tree: BinarySearchTree<String> = BinarySearchTree::new();
        tree.insert(String::from("123")); tree.insert(String::from("456"));

        assert_eq!(tree.min().unwrap(), "123");
        assert_eq!(tree.max().unwrap(), "456");
        assert_eq!(tree.sorted_vec(), vec!["123", "456"]);
    }
}
