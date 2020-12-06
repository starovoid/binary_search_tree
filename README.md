# binary_search_tree

* [Documentation](https://docs.rs/binary_search_tree/)
* [Crate](https://crates.io/crates/binary_search_tree)

A classic Binary Search Tree written in Rust.

In this implementation, each node of the binary tree contains only one useful value. To order the nodes, the elements must implement the ```Ord``` trait.

The BinarySearchTree struct provides the following methods: 
* [Viewing the root element](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.root)
* [Is the tree empty](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.is_empty)
* [Insertion](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.insert)
* [Insertion without duplicating](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.insert_without_dup)
* [Check for the presence of an element in the tree](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.contains)
* [Viewing the minimum](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.min)
* [Viewing the maximum](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.max)
* [Extracting the minimum](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.extract_min)
* [Extracting the maximum](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.extract)
* [Deleting an arbitrary value](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.remove)
* [Successor](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.successor)
* [Predecessor](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.predecessor)
* [Viewing the number of items in the tree](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.len)
* [Clearing the tree](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.clear)
* [Viewing values in the tree in ascending order](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.sorted_vec)
* [Moving the tree to a sorted vector](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.into_sorted_vec)
* [Creating a tree with elements from an iterator](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.from_iter)
* [Inorder traversal](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.inorder)
* [Preorder traversal](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.preorder)
* [Postorder traversal](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.postorder)
* [Level order traversal](https://docs.rs/binary_search_tree/0.2.0/binary_search_tree/struct.BinarySearchTree.html#method.level_order)


If you have any comments or suggestions, or you suddenly found an error, please write to prototyperailgun@gmail.com.