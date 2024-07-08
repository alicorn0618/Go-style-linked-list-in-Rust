use std::{
    cell::{Ref, RefCell, RefMut},
    fmt,
    rc::Rc,
};

pub struct List<T> {
    head: Link<T>,
    tail: Link<T>,
    len: usize,
}

pub type Link<T> = Option<NodeRef<T>>;
pub type NodeRef<V> = Rc<RefCell<Node<V>>>;

#[derive(Debug)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
    prev: Link<T>,
}

impl<T> Node<T> {
    fn new(elem: T) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Node {
            elem: elem,
            prev: None,
            next: None,
        }))
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: None,
            tail: None,
            len: 0,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push_front(&mut self, elem: T) {
        let new_head = Node::new(elem);
        self.push_node_front(new_head);
    }

    fn push_node_front(&mut self, new_head: NodeRef<T>) {
        match self.head.take() {
            Some(old_head) => {
                old_head.borrow_mut().prev = Some(new_head.clone());
                new_head.borrow_mut().next = Some(old_head);
                self.head = Some(new_head);
            }
            None => {
                self.tail = Some(new_head.clone());
                self.head = Some(new_head);
            }
        }
        self.len += 1;
    }

    pub fn push_back(&mut self, elem: T) {
        let new_tail = Node::new(elem);
        self.push_node_back(new_tail);
    }

    fn push_node_back(&mut self, new_tail: NodeRef<T>) {
        match self.tail.take() {
            Some(old_tail) => {
                old_tail.borrow_mut().next = Some(new_tail.clone());
                new_tail.borrow_mut().prev = Some(old_tail);
                self.tail = Some(new_tail);
            }
            None => {
                self.head = Some(new_tail.clone());
                self.tail = Some(new_tail);
            }
        }
        self.len += 1;
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.take().map(|old_tail| {
            match old_tail.borrow_mut().prev.take() {
                Some(new_tail) => {
                    new_tail.borrow_mut().next.take();
                    self.tail = Some(new_tail);
                }
                None => {
                    self.head.take();
                }
            }
            if self.len > 0 {
                self.len -= 1;
            }
            Rc::try_unwrap(old_tail).ok().unwrap().into_inner().elem
        })
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|old_head| {
            match old_head.borrow_mut().next.take() {
                Some(new_head) => {
                    new_head.borrow_mut().prev.take();
                    self.head = Some(new_head);
                }
                None => {
                    self.tail.take();
                }
            }
            if self.len > 0 {
                self.len -= 1;
            }
            Rc::try_unwrap(old_head).ok().unwrap().into_inner().elem
        })
    }

    pub fn peek_front(&self) -> Option<Ref<T>> {
        self.head
            .as_ref()
            .map(|node| Ref::map(node.borrow(), |node| &node.elem))
    }

    pub fn peek_back(&self) -> Option<Ref<T>> {
        self.tail
            .as_ref()
            .map(|node| Ref::map(node.borrow(), |node| &node.elem))
    }

    pub fn peek_back_mut(&mut self) -> Option<RefMut<T>> {
        self.tail
            .as_ref()
            .map(|node| RefMut::map(node.borrow_mut(), |node| &mut node.elem))
    }

    pub fn peek_front_mut(&mut self) -> Option<RefMut<T>> {
        self.head
            .as_ref()
            .map(|node| RefMut::map(node.borrow_mut(), |node| &mut node.elem))
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    pub fn remove(&mut self, node: NodeRef<T>) {
        let mut node_borrow = node.borrow_mut();
        if let Some(prev_node) = node_borrow.prev.as_ref() {
            prev_node.borrow_mut().next = node_borrow.next.clone();
        } else {
            // If there's no previous node, we're removing the head
            self.head = node_borrow.next.clone();
        }
        if let Some(next_node) = node_borrow.next.as_ref() {
            next_node.borrow_mut().prev = node_borrow.prev.clone();
        } else {
            // If there's no next node, we're removing the tail
            self.tail = node_borrow.prev.clone();
        }
        let _ = node_borrow.prev.take();
        let _ = node_borrow.next.take();
        if self.len > 0 {
            self.len -= 1;
        }
    }

    pub fn is_head(&self, node: NodeRef<T>) -> bool {
        self.head
            .as_ref()
            .map_or(false, |head| Rc::ptr_eq(head, &node))
    }

    pub fn move_to_front(&mut self, node: NodeRef<T>) {
        if self.is_head(node.clone()) {
            return;
        }
        self.remove(node.clone());
        self.push_node_front(node);
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.pop_front()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.0.pop_back()
    }
}

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "List {{ ")?;
        let mut current = self.head.clone();
        while let Some(node) = current {
            let node_borrow = node.borrow();
            write!(f, "{:?} ", node_borrow.elem)?;
            current = node_borrow.next.clone();
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod test {

    use crate::go_linked_list::Node;

    use super::List;

    #[test]
    fn basics() {
        let mut list = List::new();

        // Check empty list behaves right
        assert_eq!(list.pop_front(), None);

        // Populate list
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);

        // Check normal removal
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(2));

        // Push some more just to make sure nothing's corrupted
        list.push_front(4);
        list.push_front(5);

        // Check normal removal
        assert_eq!(list.pop_front(), Some(5));
        assert_eq!(list.pop_front(), Some(4));

        // Check exhaustion
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), None);

        // ---- back -----

        // Check empty list behaves right
        assert_eq!(list.pop_back(), None);

        // Populate list
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);

        // Check normal removal
        assert_eq!(list.pop_back(), Some(3));
        assert_eq!(list.pop_back(), Some(2));

        // Push some more just to make sure nothing's corrupted
        list.push_back(4);
        list.push_back(5);

        // Check normal removal
        assert_eq!(list.pop_back(), Some(5));
        assert_eq!(list.pop_back(), Some(4));

        // Check exhaustion
        assert_eq!(list.pop_back(), Some(1));
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn peek() {
        let mut list = List::new();
        assert!(list.peek_front().is_none());
        assert!(list.peek_back().is_none());
        assert!(list.peek_front_mut().is_none());
        assert!(list.peek_back_mut().is_none());

        list.push_front(1);
        list.push_front(2);
        list.push_front(3);

        assert_eq!(&*list.peek_front().unwrap(), &3);
        assert_eq!(&mut *list.peek_front_mut().unwrap(), &mut 3);
        assert_eq!(&*list.peek_back().unwrap(), &1);
        assert_eq!(&mut *list.peek_back_mut().unwrap(), &mut 1);
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);

        let mut iter = list.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next_back(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_remove_from_empty_list() {
        let mut list: List<i32> = List::new();
        assert!(list.is_empty());
        list.remove(Node::new(1));
        assert!(list.is_empty());
    }

    #[test]
    fn test_remove_head() {
        let mut list = List::new();
        list.push_front(1);
        list.push_front(2);

        if let Some(node_to_remove) = list.head.clone() {
            list.remove(node_to_remove);
            assert_eq!(&*list.peek_back().unwrap(), &1);
            assert_eq!(&*list.peek_front().unwrap(), &1);
        } else {
            panic!("Head node was not found");
        }
    }

    #[test]
    fn test_remove_middle() {
        let mut list = List::new();

        let node1 = Node::new(1);
        let node2 = Node::new(2);
        let node3 = Node::new(3);

        list.push_node_back(node1.clone());
        list.push_node_back(node2.clone());
        list.push_node_back(node3.clone());

        list.remove(node2);

        assert_eq!(list.len(), 2);
        assert_eq!(&*list.peek_back().unwrap(), &3);
        assert_eq!(&*list.peek_front().unwrap(), &1);
    }

    #[test]
    fn test_remove_tail() {
        let mut list = List::new();
        list.push_back(1);
        list.push_back(2);
        assert_eq!(list.len(), 2);
        if let Some(node_to_remove) = list.tail.clone() {
            list.remove(node_to_remove);
            assert_eq!(list.len(), 1);
            assert_eq!(&*list.peek_back().unwrap(), &1);
            assert!(list.peek_front().is_some());
        } else {
            panic!("Tail node was not found");
        }
    }

    #[test]
    fn test_move_to_front() {
        let mut list = List::new();
        let node1 = Node::new(1);
        let node2 = Node::new(2);
        let node3 = Node::new(3);
        let node4 = Node::new(4);
        let node5 = Node::new(5);

        list.push_node_back(node1.clone());
        list.push_node_back(node2.clone());
        list.push_node_back(node3.clone());
        list.push_node_back(node4.clone());
        list.push_node_back(node5.clone());
        assert_eq!(list.len(), 5);

        list.move_to_front(node3);
        assert_eq!(list.len(), 5);
        assert_eq!(&*list.peek_front().unwrap(), &3);

        list.move_to_front(node2);
        assert_eq!(list.len(), 5);
        assert_eq!(&*list.peek_front().unwrap(), &2);
    }
}
