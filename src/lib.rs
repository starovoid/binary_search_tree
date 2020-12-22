//! This module contains an implementation of a classic binary search tree 
//! with a large set of methods, including view iterators. 

use std::fmt;
use std::cmp::{ Ordering, PartialEq };
use std::iter::{ FromIterator, Extend };
use std::collections::VecDeque;

/// In this crate, binary search trees store only one valuable value, which is also 
/// used as a key, so all elements must have the ```Ord``` trait implementation.
/// 
/// # Examples
/// 
/// ```
/// extern crate binary_search_tree;
/// 
/// use binary_search_tree::BinarySearchTree;
/// 
/// // Create a new binary search tree and fill it with numbers from 1 to 5:
/// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
/// for i in vec![3, 1, 2, 5, 4] {
///     tree.insert(i);
/// }
/// 
/// // Get them in sorted order
/// assert_eq!(tree.sorted_vec(), vec![&1, &2, &3, &4, &5]);
/// 
/// // Let's extract the minimum and maximum.
/// assert_eq!(tree.extract_min(), Some(1));
/// assert_eq!(tree.extract_max(), Some(5));
/// assert_eq!(tree.sorted_vec(), vec![&2, &3, &4]);
/// 
/// // We can also extend the tree with elements from the iterator.
/// tree.extend((0..6).map(|x| if x%2 == 0 { x } else { -x }));
/// assert_eq!(tree.len(), 9);
/// 
/// // If the elements must be unique, you should use insert_without_dup().
/// tree.insert_without_dup(0);
/// assert_eq!(tree.len(), 9);
/// 
/// // Delete the value 0 from the tree and make sure that the deletion actually occurred.
/// tree.remove(&0);
/// assert!(!tree.contains(&0));
/// 
/// // We can clear the tree of any remaining items.
/// tree.clear();
/// 
/// // The tree should now be empty.
/// assert!(tree.is_empty());
/// ``` 


#[derive(Debug)]
pub struct BinarySearchTree<T: Ord> {
    root: Tree<T>,
    pub size: usize,
}

#[derive(Debug)]
struct Node<T: Ord> {
    value: T,
    left: Tree<T>,
    right: Tree<T>,
}

#[derive(Debug)]
struct Tree<T: Ord>(Option<Box<Node<T>>>);


impl<T: Ord> PartialEq for BinarySearchTree<T> {
    fn eq(&self, other: &BinarySearchTree<T>) -> bool {
        self.sorted_vec() == other.sorted_vec()
    }
}

impl<T: Ord + fmt::Debug> fmt::Display for BinarySearchTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.sorted_vec())
    }
}

impl<T: Ord> Extend<T> for BinarySearchTree<T> {
    /// Extend bst with elements from the iterator.
    /// 
    /// Note: extend doesn't keep track of duplicates, but just uses the whole iterator.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// use std::iter::Extend;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.extend(vec![7, 1, 0, 4, 5, 3].into_iter());
    /// assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);
    /// ```
    fn extend<I: IntoIterator<Item=T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |elem| { 
            self.insert(elem); 
        });
    }
}

impl<T: Ord> FromIterator<T> for BinarySearchTree<T> {
    /// Сreating a bst from an iterator.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// use std::iter::FromIterator;
    /// 
    /// let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(
    ///     vec![7, 1, 0, 4, 5, 3].into_iter());
    /// assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);
    /// 
    /// let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 5, 3].into_iter().collect();
    /// assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);
    /// ```
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let mut tree = BinarySearchTree::new();
        tree.extend(iter);
        tree
    }
}

impl<T: Ord + Clone> Clone for BinarySearchTree<T> {
    fn clone(&self) -> BinarySearchTree<T> {
        let mut new_tree = BinarySearchTree::new();

        for elem in self.sorted_vec().iter() {
            new_tree.insert((*elem).clone());
        }

        new_tree
    }
}


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
        BinarySearchTree { root: Tree(None), size: 0 }
    }
    
    /// Сhecking if the tree is empty.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(tree.is_empty());
    /// 
    /// tree.insert(1);
    /// assert!(!tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
    
    /// Returns the number of elements in the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    ///
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.len(), 0);
    /// tree.insert(1);
    /// assert_eq!(tree.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }
    
    /// Clears the binary search tree, removing all elements.
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
    
    /// Viewing the root element of the tree.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(tree.root().is_none());  // is empty
    /// 
    /// tree.insert(1); tree.insert(0); tree.insert(2);
    /// 
    /// // the first element inserted becomes the root
    /// assert_eq!(tree.root(), Some(&1));
    /// ```
    pub fn root(&self) -> Option<&T> {
        self.root.0.as_ref().map(|node| &node.value)
    }
    
    /// Inserting a new element.
    ///
    /// Returns true if an element with the same value already exists in the tree, false otherwise.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// 
    /// assert!(!tree.insert(1)); 
    /// assert!(!tree.insert(0)); 
    /// assert!(!tree.insert(2));
    /// assert!(tree.insert(1));  // element 1 is already in the tree
    /// 
    /// assert_eq!(tree.size, 4);
    /// 
    /// // Elements in sorted order (inorder traversal)
    /// assert_eq!(tree.sorted_vec(), vec![&0, &1, &1, &2]);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.size += 1;
        self.root.insert(value, true)
    }
    
    /// Inserting a new unique element.
    /// 
    /// If an element with the same value is already in the tree, the insertion will not happen.
    /// Returns true if an element with the same value already exists in the tree, false otherwise.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// 
    /// assert!(!tree.insert_without_dup(1)); 
    /// assert!(!tree.insert_without_dup(0)); 
    /// assert!(!tree.insert_without_dup(2));
    /// assert!(tree.insert_without_dup(1));  // element 1 is already in the tree
    /// 
    /// assert_eq!(tree.size, 3);
    /// 
    /// // Elements in sorted order (inorder traversal)
    /// assert_eq!(tree.sorted_vec(), vec![&0, &1, &2]);
    /// ```
    pub fn insert_without_dup(&mut self, value: T) -> bool {
        let res = self.root.insert(value, false);
        if !res {
            self.size += 1;
        }
        res
    }
    
    /// Checks whether the tree contains an element with the specified value.
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
    /// assert!(tree.contains(&2));
    /// assert!(tree.contains(&1));
    /// assert!(!tree.contains(&999));
    /// ```
    pub fn contains(&self, target: &T) -> bool {
        self.root.contains(target)
    }
    
    /// The minimum element of the tree.
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
    /// assert_eq!(tree.min(), Some(&0));
    pub fn min(&self) -> Option<&T> {
        self.root.min()
    }
    
    /// The maximum element of the tree.
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
    /// assert_eq!(tree.max(), Some(&2));
    /// ```
    pub fn max(&self) -> Option<&T> {
        self.root.max()
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
    /// assert_eq!(tree.successor(&25), Some(&35));
    /// 
    /// assert_eq!(tree.successor(&40), Some(&45));
    /// assert!(tree.successor(&45).is_none()); // Element 45 has no successors
    /// 
    /// // We can also find successors for missing values in the tree
    /// assert_eq!(tree.successor(&20), Some(&25)); // [..., &18, vv &20 vv, &25, ...]
    /// ```
    pub fn successor(&self, val: &T) -> Option<&T> {
        self.root.successor(val)
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
    /// assert_eq!(tree.predecessor(&25), Some(&18));
    /// 
    /// assert_eq!(tree.predecessor(&40), Some(&35));
    /// assert!(tree.predecessor(&10).is_none()); // Element 10 has no predecessors
    /// 
    /// // We can also find predecessors for missing values in the tree
    /// assert_eq!(tree.predecessor(&20), Some(&18)); // [..., &18, vv &20 vv, &25, ...]
    /// ```
    pub fn predecessor(&self, val: &T) -> Option<&T> {
        self.root.predecessor(val)
    }
    
    /// Remove and return the minimum element.
    /// 
    /// This operation is much more efficient than searching for the 
    /// minimum and then deleting it, since only one pass is performed 
    /// and there are no comparisons between elements at all.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(tree.extract_min().is_none());
    /// 
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// 
    /// assert_eq!(tree.extract_min(), Some(10));
    /// assert_eq!(tree.extract_min(), Some(15));
    /// 
    /// assert_eq!(tree.sorted_vec(), vec![&25, &40]);
    /// ```
    pub fn extract_min(&mut self) -> Option<T> {
        let res = self.root.extract_min();
        if res.is_some() {
            self.size -= 1;
        }
        res
    }
    
    /// Remove and return the maximum element.
    /// 
    /// This operation is much more efficient than searching for the 
    /// maximum and then deleting it, since only one pass is performed 
    /// and there are no comparisons between elements at all.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(tree.extract_max().is_none());
    /// 
    /// tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);
    /// 
    /// assert_eq!(tree.extract_max(), Some(40));
    /// assert_eq!(tree.extract_max(), Some(25));
    /// 
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15]);
    /// ```
    pub fn extract_max(&mut self) -> Option<T> {
        let res = self.root.extract_max();
        if res.is_some() {
            self.size -= 1;
        }
        res
    }
    
    /// Remove the first occurrence of an element with the target value.
    /// 
    /// Returns true if deletion occurred and false if target is missing from the tree.
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
    /// assert!(tree.remove(&18));
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &25, &35, &40, &45]);
    /// assert_eq!(tree.size, 7);
    /// 
    /// tree.remove(&25);
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &35, &40, &45]);
    /// assert_eq!(tree.size, 6);
    /// 
    /// // If you try to delete a value that is missing from the tree, nothing will change
    /// assert!(!tree.remove(&99));
    /// assert_eq!(tree.sorted_vec(), vec![&10, &15, &18, &35, &40, &45]);
    /// assert_eq!(tree.size, 6);
    /// ```
    pub fn remove(&mut self, target: &T) -> bool {
        let res = self.root.remove(target);
        if res {
            self.size -= 1;
        }
        res
    }
    
    /// Vector of references to elements in the tree in non-decreasing order.
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
        self.root.sorted_vec()
    }
    
    /// Moving the tree to a sorted vector.
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
        self.root.into_sorted_vec()
    }
    
    /// Inorder traverse iterator of binary search tree.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = vec![5, 7, 3, 4, 8, 6, 1].into_iter().collect();
    /// // Now we have a tree that looks like this:
    /// //                  5
    /// //               3     7
    /// //              1 4   6 8
    /// 
    /// // And we should get the following sequence of its elements: 1, 3, 4, 5, 6, 7, 8
    /// assert_eq!(tree.inorder().collect::<Vec<&i32>>(), vec![&1, &3, &4, &5, &6, &7, &8]);
    /// ```
    pub fn inorder(&self) -> InorderTraversal<T> {
        InorderTraversal { 
            stack: Vec::new(), 
            current: self.root.0.as_ref(),
        }
    }
    
    /// Reverse order traverse iterator of binary search tree.
    /// 
    /// This iterator traverses the elements of the tree in descending order.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = vec![5, 7, 3, 4, 8, 6, 1].into_iter().collect();
    /// // Now we have a tree that looks like this:
    /// //                  5
    /// //               3     7
    /// //              1 4   6 8
    /// 
    /// // And we should get the following sequence of its elements: 8, 7, 6, 5, 4, 3, 1
    /// assert_eq!(tree.reverse_order().collect::<Vec<&i32>>(), vec![&8, &7, &6, &5, &4, &3, &1]);
    /// ```
    pub fn reverse_order(&self) -> ReverseOrderTraversal<T> {
        ReverseOrderTraversal {
            stack: Vec::new(),
            current: self.root.0.as_ref(),
        }
    }
    
    /// Preorder traverse iterator of binary search tree.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = vec![5, 7, 3, 4, 8, 6, 1].into_iter().collect();
    /// // Now we have a tree that looks like this:
    /// //                  5
    /// //               3     7
    /// //              1 4   6 8
    /// 
    /// // And we should get the following sequence of its elements: 5, 3, 1, 4, 7, 6, 8
    /// assert_eq!(tree.preorder().collect::<Vec<&i32>>(), vec![&5, &3, &1, &4, &7, &6, &8]);
    /// ```
    pub fn preorder(&self) -> PreorderTraversal<T> {
        PreorderTraversal {
            stack: vec![self.root.0.as_ref()],
            current: self.root.0.as_ref(),
        }
    }
    
    /// Postorder traverse iterator of binary search tree.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = vec![5, 7, 3, 4, 8, 6, 1].into_iter().collect();
    /// // Now we have a tree that looks like this:
    /// //                  5
    /// //               3     7
    /// //              1 4   6 8
    /// 
    /// // And we should get the following sequence of its elements: 1, 4, 3, 6, 8, 7, 5
    /// assert_eq!(tree.postorder().collect::<Vec<&i32>>(), vec![&1, &4, &3, &6, &8, &7, &5]);
    /// ```
    pub fn postorder(&self) -> PostorderTraversal<T> {
        PostorderTraversal {
            stack: Vec::new(),
            current: self.root.0.as_ref(),
        }
    }
    
    /// Level order binary tree traversal.
    /// # Examples
    /// 
    /// ```
    /// use binary_search_tree::BinarySearchTree;
    /// 
    /// let tree: BinarySearchTree<i32> = vec![5, 7, 3, 4, 8, 6, 1].into_iter().collect();
    /// // Now we have a tree that looks like this:
    /// //                  5
    /// //               3     7
    /// //              1 4   6 8
    /// 
    /// // And we should get the following sequence of its elements: 5, 3, 7, 1, 4, 6, 8
    /// assert_eq!(tree.level_order().collect::<Vec<&i32>>(), vec![&5, &3, &7, &1, &4, &6, &8]);
    /// ```
    pub fn level_order(&self) -> LevelOrderTraversal<T> {
        let mut deque = VecDeque::new();
        if let Some(root) = self.root.0.as_ref() {
            deque.push_back(root);
        }
        LevelOrderTraversal { deque: deque }
    }
}


impl<T: Ord> Node<T> {
    pub fn new(value: T) -> Self {
        Node {
            value: value,
            left: Tree(None),
            right: Tree(None),
        }
    }
}


impl<T: Ord> Tree<T> {
    /// Inserting a new element in the tree
    /// Returns true if an element with the same value already exists in the tree
    pub fn insert(&mut self, value: T, allow_duplicate: bool) -> bool {
        let mut current = self;
        let mut is_duplicate = false;
        
        // Follow from the root to the leaves in search of a place to insert
        while let Some(ref mut node) = current.0 {
            match node.value.cmp(&value) {
                Ordering::Greater => current = &mut node.left,
                Ordering::Less => current = &mut node.right,
                Ordering::Equal => {
                    if allow_duplicate {
                        is_duplicate = true;
                        current = &mut node.right;
                    } else {
                        return true;
                    }
                }
            }
        }
        
        // A suitable position is found, replace None with a new node
        current.0 = Some(Box::new(Node::new(value)));
        
        is_duplicate
    }
    
    /// Checks whether the tree contains an element with the specified value
    pub fn contains(&self, target: &T) -> bool {
        let mut current = self;
        
        // Follow from the root to the leaves in search of the set value
        while let Some(ref node) = current.0 {
            match node.value.cmp(target) {
                Ordering::Greater => current = &node.left,
                Ordering::Less => current = &node.right,
                Ordering::Equal => return true,
            }
        }

        false
    }
    
    /// The minimum element of the tree
    pub fn min(&self) -> Option<&T> {
        if self.0.is_some() {
            
            let mut current = self.0.as_ref();
            let mut left = current.unwrap().left.0.as_ref();
            
            while let Some(node) = left {
                current = left;
                left = node.left.0.as_ref();
            }
            
            current.map(|node| &node.value)

        } else {
            None
        }
    }
    
    /// The maximum element of the tree
    pub fn max(&self) -> Option<&T> {
        if self.0.is_some() {
            
            let mut current = self.0.as_ref();
            let mut right = current.unwrap().right.0.as_ref();
            
            while let Some(node) = right {
                current = right;
                right = node.right.0.as_ref();
            }
            
            current.map(|node| &node.value)

        } else {
            None
        }
    }
    
    /// Inorder successor of the element with the specified value
    pub fn successor(&self, val: &T) -> Option<&T> {
        let mut current = self.0.as_ref();
        let mut successor = None;

        while current.is_some() {
            let node = current.unwrap();

            if node.value > *val {
                successor = current;
                current = node.left.0.as_ref();
            } else {
                current = node.right.0.as_ref();
            }
        }

        successor.map(|node| &node.value)
    }
    
    /// Inorder predecessor of the element with the specified value
    pub fn predecessor(&self, val: &T) -> Option<&T> {
        let mut current = self.0.as_ref();
        let mut predecessor = None;

        while current.is_some() {
            let node = current.unwrap();
            if node.value < *val {
                predecessor = current;
                current = node.right.0.as_ref();
            } else {
                current = node.left.0.as_ref();
            }
        }

        predecessor.map(|node| &node.value)
    }
    
    /// Remove and return the minimum element
    pub fn extract_min(&mut self) -> Option<T> {
        let mut to_return = None;

        if self.0.is_some() {
            let mut current = self;
            
            // Finding the last non-empty node in the left branch
            while current.0.as_ref().unwrap().left.0.is_some() {
                current = &mut current.0.as_mut().unwrap().left;
            }
            
            // The minimum element is replaced by its right child (the right child can be empty)
            let node = current.0.take().unwrap();
            to_return = Some(node.value);
            current.0 = node.right.0;
        }

        to_return
    }
    
    /// Remove and return the maximum element
    pub fn extract_max(&mut self) -> Option<T> {
        let mut to_return = None;

        if self.0.is_some() {
            let mut current = self;
            
            // Finding the last non-empty node in the right branch
            while current.0.as_ref().unwrap().right.0.is_some() {
                current = &mut current.0.as_mut().unwrap().right;
            }
            
            // The maximum element is replaced by its left child (the left child can be empty)
            let node = current.0.take().unwrap();
            to_return = Some(node.value);
            current.0 = node.left.0;
        }

        to_return
    }
    
    /// Deleting the first occurrence of an element with the specified value
    pub fn remove(&mut self, target: &T) -> bool {
        let mut current: *mut Tree<T> = self;
        
        unsafe {
            while let Some(ref mut node) = (*current).0 {
                match node.value.cmp(target) {
                    Ordering::Greater => {
                        current = &mut node.left;
                    },
                    Ordering::Less => { 
                        current = &mut node.right;
                    },
                    Ordering::Equal => {
                        match (node.left.0.as_mut(), node.right.0.as_mut()) {
                            // The node has no childrens, so we'll just make it empty.
                            (None, None) => {
                                (*current).0 = None;
                            },
                            // Replace the node with its left child
                            (Some(_), None) => {
                                (*current).0 = node.left.0.take();
                            },
                            // Replace the node with its left child
                            (None, Some(_)) => {
                                (*current).0 = node.right.0.take();
                            },
                            // The most complexity case: replace the value of the current node with 
                            // its successor and then remove the successor's node.
                            // The BST invariant is not violated, which is easy to verify
                            (Some(_), Some(_)) => {
                                (*current).0.as_mut().unwrap().value = node.right.extract_min().unwrap();
                            }
                        }

                        return true; // The removal occurred
                    }, 
                }
            }
        }
        
        false // The element with the 'target' value was not found
    }
    
    // Vector of links to tree elements in sorted order
    pub fn sorted_vec(&self) -> Vec<&T> {
        let mut elements = Vec::new();
        
        if let Some(node) = self.0.as_ref() {
            elements.extend(node.left.sorted_vec());
            elements.push(&node.value);
            elements.extend(node.right.sorted_vec());
        }

        elements
    }
    
    /// Moving the tree into a sorted vector
    pub fn into_sorted_vec(self) -> Vec<T> {
        let mut elements = Vec::new();
        
        if let Some(node) = self.0 {
            elements.extend(node.left.into_sorted_vec());
            elements.push(node.value);
            elements.extend(node.right.into_sorted_vec());
        }

        elements
    }
}


pub struct InorderTraversal<'a, T: 'a + Ord> {
    stack: Vec<Option<&'a Box<Node<T>>>>,
    current: Option<&'a Box<Node<T>>>,
}

pub struct ReverseOrderTraversal<'a, T: 'a + Ord> {
    stack: Vec<Option<&'a Box<Node<T>>>>,
    current: Option<&'a Box<Node<T>>>,
}

pub struct PreorderTraversal<'a, T: 'a + Ord> {
    stack: Vec<Option<&'a Box<Node<T>>>>,
    current: Option<&'a Box<Node<T>>>,
}

pub struct PostorderTraversal<'a, T: 'a + Ord> {
    stack: Vec<Option<&'a Box<Node<T>>>>,
    current: Option<&'a Box<Node<T>>>,
}

pub struct LevelOrderTraversal<'a, T: 'a + Ord> {
    deque: VecDeque<&'a Box<Node<T>>>,
}


impl<'a, T: 'a + Ord> Iterator for InorderTraversal<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<&'a T> {
        loop {
            if let Some(current) = self.current {
                self.stack.push(self.current);
                self.current = current.left.0.as_ref();
            } else {
                if let Some(node) = self.stack.pop() {
                    let current = node.unwrap();
                    let elem = &current.value;
                    self.current = current.right.0.as_ref();
                    return Some(elem);
                } else {
                    return None;
                }
            }
        }
    }
}

impl<'a, T: 'a + Ord> Iterator for ReverseOrderTraversal<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<&'a T> {
        loop {
            if let Some(current) = self.current {
                self.stack.push(self.current);
                self.current = current.right.0.as_ref();
            } else {
                if let Some(node) = self.stack.pop() {
                    let current = node.unwrap();
                    let elem = &current.value;
                    self.current = current.left.0.as_ref();
                    return Some(elem);
                } else {
                    return None;
                }
            }
        }
    }
}

impl<'a, T: 'a + Ord> Iterator for PreorderTraversal<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<&'a T> {
        loop {
            if let Some(current) = self.current {
                let elem = &current.value;
                self.current = current.left.0.as_ref();
                self.stack.push(self.current);
                return Some(elem);
            } else {
                if let Some(node) = self.stack.pop() {
                    if let Some(current) = node {
                        self.current = current.right.0.as_ref();
                        if self.current.is_some() {
                            self.stack.push(self.current);
                        }
                    }
                } else {
                    return None;
                }
            }
        }
    }
}

impl<'a, T: 'a + Ord> Iterator for PostorderTraversal<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<&'a T> {
        loop {
            // Go down the left branch and add nodes along with their right chilfren to the stack
            while let Some(current) = self.current {
                if current.right.0.is_some() {
                    self.stack.push(current.right.0.as_ref());
                }
                self.stack.push(self.current);
                self.current = current.left.0.as_ref();
            }

            if self.stack.len() == 0 {
                return None;
            }
            
            if let Some(root) = self.stack.pop().unwrap() {
                // If the popped item has a right child and the 
                // right child is not processed yet, then make sure 
                // right child is processed before root 
                if self.stack.len() > 0 && root.right.0.is_some() && 
                    self.stack.get(self.stack.len()-1)
                        .unwrap().unwrap().value == root.right.0.as_ref().unwrap().value {

                    self.stack.pop();            // Remove right child from stack
                    self.stack.push(Some(root)); // Push root back to stack

                    // Changing the current node so that the root's right child is viewed first
                    self.current = root.right.0.as_ref();

                } else {
                    let elem = &root.value;
                    self.current = None;
                    return Some(elem);
                }

            } else {
                return None; // Only empty nodes remain
            }
        }
    }
}

impl<'a, T: 'a + Ord> Iterator for LevelOrderTraversal<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if let Some(boxed_node) = self.deque.pop_front() {
            if let Some(left) = boxed_node.left.0.as_ref() {
                self.deque.push_back(left);
            }
            if let Some(right) = boxed_node.right.0.as_ref() {
                self.deque.push_back(right);
            }
            Some(&boxed_node.value)
        } else {
            return None
        }
    }
}

#[cfg(test)]
mod test;