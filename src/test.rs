use crate::BinarySearchTree;
use std::iter::FromIterator;

#[test]
fn basics() {
    let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    
    //Check empty bst behaves right
    assert_eq!(tree.is_empty(), true);
    assert_eq!(tree.size, 0);
    assert_eq!(tree.min(), None);
    assert_eq!(tree.max(), None);
    assert_eq!(tree.contains(&5), false);
    assert!(!tree.remove(&99));

    // Populate bst
    assert!(!tree.insert(1)); 

    //Check one-element bst behaves right
    assert!(!tree.is_empty());
    assert_eq!(tree.size, 1);
    assert_eq!(tree.min(), Some(&1));
    assert_eq!(tree.max(), Some(&1));
    assert!(!tree.contains(&5));
    assert!(tree.contains(&1));

    // Populate bst
    assert!(!tree.insert(0)); 
    assert!(!tree.insert(-2)); 
    assert!(!tree.insert(5));
    assert!(tree.insert(5));   // element 5 is already in the tree
    assert!(!tree.insert(15)); 
    assert!(!tree.insert(-5)); 
    assert!(!tree.insert(3));
    assert!(tree.insert(0));   // element 0 is already in the tree

    assert_eq!(tree.size, 9);
    assert_eq!(tree.root().unwrap(), &1);
    assert_eq!(tree.sorted_vec(), vec![&-5, &-2, &0, &0, &1, &3, &5, &5, &15]);

    // Checking the operation of min(), max()
    assert_eq!(tree.min().unwrap(), &-5);
    assert_eq!(tree.max().unwrap(), &15);

    // Checking the operation of contains
    assert_eq!(tree.contains(&-5), true);
    assert_eq!(tree.contains(&0), true);
    assert_eq!(tree.contains(&55), false);

    // Checking the tree structure
    assert_eq!(tree.sorted_vec(), vec![&-5, &-2, &0, &0, &1, &3, &5, &5, &15]);
    
    assert!(!tree.remove(&100));
    assert_eq!(tree.sorted_vec(), vec![&-5, &-2, &0, &0, &1, &3, &5, &5, &15]);
    assert!(tree.remove(&-5));
    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &0, &1, &3, &5, &5, &15]);
    assert!(tree.remove(&0));
    assert!(!tree.remove(&-100));
    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &3, &5, &5, &15]);
    assert!(tree.remove(&5));
    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &3, &5, &15]);
    assert!(tree.remove(&15));
    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &3, &5]);
    assert!(tree.remove(&1));
    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &3, &5]);
    assert!(tree.remove(&-2));
    assert_eq!(tree.sorted_vec(), vec![&0, &3, &5]);
    assert!(tree.remove(&5));
    assert_eq!(tree.sorted_vec(), vec![&0, &3]);
    assert!(tree.remove(&0));
    assert_eq!(tree.sorted_vec(), vec![&3]);
    assert!(tree.remove(&3));
    assert!(tree.is_empty());
    assert_eq!(tree.size, 0);
}

#[test]
fn insert_without_duplication() {
    let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert!(!tree.insert_without_dup(0));
    assert!(!tree.insert_without_dup(1));
    assert!(tree.insert_without_dup(0));

    assert_eq!(tree.sorted_vec(), vec![&0, &1]);
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
fn extract_min() {
    let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert!(tree.extract_min().is_none());

    tree.insert(0);
    assert_eq!(tree.extract_min(), Some(0));
    assert!(tree.is_empty());
    assert_eq!(tree.size, 0);

    tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);

    assert_eq!(tree.extract_min(), Some(10));
    assert_eq!(tree.sorted_vec(), vec![&15, &25, &40]);

    assert_eq!(tree.extract_min(), Some(15));
    assert_eq!(tree.extract_min(), Some(25));
    assert_eq!(tree.extract_min(), Some(40));

    assert!(tree.is_empty());
    assert_eq!(tree.size, 0);
}

#[test]
fn extract_max() {
    let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert!(tree.extract_max().is_none());

    tree.insert(0);
    assert_eq!(tree.extract_max(), Some(0));
    assert!(tree.is_empty());
    assert_eq!(tree.size, 0);

    tree.insert(25); tree.insert(15); tree.insert(40); tree.insert(10);

    assert_eq!(tree.extract_max(), Some(40));
    assert_eq!(tree.sorted_vec(), vec![&10, &15, &25]);

    assert_eq!(tree.extract_max(), Some(25));
    assert_eq!(tree.extract_max(), Some(15));
    assert_eq!(tree.extract_max(), Some(10));

    assert!(tree.is_empty());
    assert_eq!(tree.size, 0);
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

    assert_eq!(1.clone(), 1);

    let mut cloned = tree.clone();
    cloned.insert(99); cloned.remove(&0);

    assert_eq!(tree.sorted_vec(), vec![&-2, &0, &1, &5]);
    assert_eq!(cloned.sorted_vec(), vec![&-2, &1, &5, &99]);

    let mut tree: BinarySearchTree<String> = BinarySearchTree::new();
    tree.insert("Hello".to_string()); tree.insert("World".to_string());
    
    let mut cloned = tree.clone();
    cloned.extract_min();

    assert_eq!(tree.sorted_vec(), vec![&"Hello", &"World"]);
    assert_eq!(cloned.sorted_vec(), vec![&"World"]);
}

#[test]
fn extend() {
    let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    tree.extend(vec![7, 1, 0, 4, 5, 3].into_iter());
    assert_eq!(tree.len(), 6);
    assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);
}

#[test]
fn from_iter() {
    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(Vec::new().into_iter());
    assert!(tree.is_empty());

    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(
        vec![7, 1, 0, 4, 5, 3].into_iter()
    );
    assert_eq!(tree.len(), 6);
    assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);

    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 5, 3].into_iter().collect();
    assert_eq!(tree.len(), 6);
    assert_eq!(tree.sorted_vec(), [&0, &1, &3, &4, &5, &7]);
}

#[test]
fn inorder() {
    let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert_eq!(tree.inorder().collect::<Vec<&i32>>().len(), 0);

    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(vec![0].into_iter());
    assert_eq!(tree.inorder().collect::<Vec<&i32>>(), vec![&0]);

    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    assert_eq!(tree.inorder().collect::<Vec<&i32>>(), vec![&0, &1, &2, &3, &4, &5, &6, &7, &8]);
    assert_eq!(tree.sorted_vec(), vec![&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}

#[test]
fn preorder() {
    let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert_eq!(tree.preorder().collect::<Vec<&i32>>().len(), 0);

    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(vec![0].into_iter());
    assert_eq!(tree.preorder().collect::<Vec<&i32>>(), vec![&0]);

    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    assert_eq!(tree.preorder().collect::<Vec<&i32>>(), vec![&7, &1, &0, &4, &2, &3, &5, &6, &8]);
    assert_eq!(tree.sorted_vec(), vec![&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}

#[test]
fn postorder() {
    let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert_eq!(tree.postorder().collect::<Vec<&i32>>().len(), 0);

    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(vec![0].into_iter());
    assert_eq!(tree.postorder().collect::<Vec<&i32>>(), vec![&0]);

    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    assert_eq!(tree.postorder().collect::<Vec<&i32>>(), vec![&0, &3, &2, &6, &5, &4, &1, &8, &7]);
    assert_eq!(tree.sorted_vec(), vec![&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}

#[test]
fn level_order() {
    let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    assert_eq!(tree.level_order().collect::<Vec<&i32>>().len(), 0);

    let tree: BinarySearchTree<i32> = BinarySearchTree::from_iter(vec![0].into_iter());
    assert_eq!(tree.level_order().collect::<Vec<&i32>>(), vec![&0]);

    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    assert_eq!(tree.level_order().collect::<Vec<&i32>>(), vec![&7, &1, &8, &0, &4, &2, &5, &3, &6]);
    assert_eq!(tree.sorted_vec(), vec![&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}

#[test]
fn partail_eq() {
    let first: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    let second: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    assert!(first == second);

    let first: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    let second: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2].into_iter().collect();
    assert!(first != second);

    let first: BinarySearchTree<i32> = BinarySearchTree::new();
    let second: BinarySearchTree<i32> = BinarySearchTree::new();
    assert!(first == second);

    let first: BinarySearchTree<String> = vec!["abc".to_string(), "efg".to_string()].into_iter().collect();
    let second: BinarySearchTree<String> = vec!["abc".to_string(), "efg".to_string()].into_iter().collect();
    assert!(first == second);

    let first: BinarySearchTree<String> = vec!["abc".to_string(), "efg".to_string()].into_iter().collect();
    let second: BinarySearchTree<String> = vec!["abc".to_string()].into_iter().collect();
    assert!(first != second);
}

#[test]
fn display() {
    let tree: BinarySearchTree<i32> = vec![7, 1, 0, 4, 2, 5, 3, 6, 8].into_iter().collect();
    println!("{}", tree);
    let tree: BinarySearchTree<String> = vec!["abc".to_string(), "efg".to_string()].into_iter().collect();
    println!("{}", tree);
}