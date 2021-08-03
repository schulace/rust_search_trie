use std::collections::hash_map::Iter as HashMapIter;
use std::collections::HashMap;
use std::fmt::{self, Display};

#[derive(Debug, Default, Clone)]
pub struct SearchTrie<T> {
    successors: HashMap<T, SearchTrie<T>>,
    is_word_end: bool,
}

impl<T> Display for SearchTrie<T>
where
    T: Display + Ord,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.display_self(fmt, 0)
    }
}

impl<T> SearchTrie<T>
where
    T: Display + Ord,
{
    fn display_self(&self, fmt: &mut fmt::Formatter, indent_level: usize) -> fmt::Result {
        let pairs = {
            let mut tmp: Vec<(&T, &Self)> = self.successors.iter().collect();
            tmp.sort_by_key(|(v, _)| *v);
            tmp
        };
        pairs
            .iter()
            .map(|(letter, subtree)| {
                writeln!(
                    fmt,
                    "{ilvl}{letter}{end_punct}",
                    ilvl = str::repeat(" ", indent_level),
                    letter = letter,
                    end_punct = if subtree.is_word_end { "!" } else { "" }
                )
                .and_then(|_| subtree.display_self(fmt, indent_level + 1))
            })
            .collect()
    }
}

impl<T> SearchTrie<T>
where
    T: std::cmp::Eq,
    T: std::hash::Hash,
{
    pub fn successor_for(&self, letter: &T) -> Option<&Self> {
        self.successors.get(letter)
    }

    pub fn successor_for_mut(&mut self, letter: &T) -> Option<&mut Self> {
        self.successors.get_mut(letter)
    }

    pub fn insert_word(&mut self, mut word: Vec<T>) -> bool {
        match word.len() {
            0 => {
                if self.is_word_end {
                    true
                } else {
                    self.is_word_end = true;
                    false
                }
            }
            _ => {
                let next_letter = word.remove(0);
                if let Some(child) = self.successor_for_mut(&next_letter) {
                    child.insert_word(word)
                } else {
                    let mut child = SearchTrie {
                        successors: Default::default(),
                        is_word_end: false,
                    };
                    child.insert_word(word);
                    self.successors.insert(next_letter, child);
                    false
                }
            }
        }
    }

    pub fn remove_word(&mut self, word: &[T]) {
        match word.len() {
            0 => {
                self.is_word_end = false;
            }
            1 => {
                if let Some(next_trie) = self.successors.get_mut(&word[0]) {
                    if next_trie.successors.len() == 0 {
                        // cleanup so we don't just have empty subtrees
                        self.successors.remove(&word[0]);
                    } else {
                        next_trie.is_word_end = false;
                    }
                }
            }
            _ => {
                self.successors
                    .get_mut(&word[0])
                    .map(|subtree| subtree.remove_word(&word[1..]));
            }
        }
    }

    pub fn contains_word(&self, word: &[T]) -> bool {
        match word.len() {
            0 => self.is_word_end,
            _ => self
                .successors
                .get(&word[0])
                .map(|rst| rst.contains_word(&word[1..]))
                .unwrap_or(false),
        }
    }
}

impl<T> SearchTrie<T> {
    pub fn iter(&self) -> SearchTrieIterator<T> {
        SearchTrieIterator {
            root_trie: &self,
            current_iter: self.successors.iter(),
            parent_letter: None,
            sub_iter: None,
            is_exhausted: false,
        }
    }
    pub fn new() -> Self {
        SearchTrie {
            successors: HashMap::new(),
            is_word_end: false,
        }
    }
}

/// constructed by calling `SearchTrie::iter()`
pub struct SearchTrieIterator<'a, T> {
    root_trie: &'a SearchTrie<T>,
    current_iter: HashMapIter<'a, T, SearchTrie<T>>,
    parent_letter: Option<&'a T>,
    sub_iter: Option<Box<SearchTrieIterator<'a, T>>>,
    is_exhausted: bool,
}

impl<'a, T> SearchTrieIterator<'a, T> {
    fn internal_next(&mut self) -> Option<Vec<&'a T>> {
        if self.is_exhausted {
            return None;
        };
        match &mut self.sub_iter {
            Some(child_iterator) => match child_iterator.internal_next() {
                Some(mut v) => {
                    if let Some(character) = self.parent_letter {
                        v.push(character);
                    }
                    Some(v)
                }
                // child iterator is exhausted, re-execute `sub_iter is None` case
                None => {
                    self.sub_iter = None;
                    self.internal_next()
                }
            },
            None => match self.current_iter.next() {
                Some((k, v)) => {
                    self.sub_iter = Some(Box::new(v.iter()));
                    self.parent_letter = Some(k);
                    self.internal_next()
                }
                None => {
                    self.is_exhausted = true;
                    if self.root_trie.is_word_end {
                        Some(vec![])
                    } else {
                        None
                    }
                }
            },
        }
    }
}

impl<'a, T> Iterator for SearchTrieIterator<'a, T> {
    type Item = Vec<&'a T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.internal_next().map(|mut v| {
            v.reverse();
            v
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn one_word() {
        let mut tree: SearchTrie<u8> = Default::default();
        tree.insert_word(vec![1, 2, 3]);
        assert!(tree.contains_word(&[1, 2, 3]));
        assert_eq!(tree.contains_word(&[]), false);
    }
    #[test]
    fn substrings() {
        let mut tree: SearchTrie<u8> = Default::default();
        tree.insert_word(vec![1, 2, 3]);
        tree.insert_word(vec![1, 2]);
        assert!(tree.contains_word(&[1, 2, 3]));
        assert!(tree.contains_word(&[1, 2]));
        assert_eq!(tree.contains_word(&[]), false);
        let mut tree: SearchTrie<u8> = Default::default();
        tree.insert_word(vec![1, 2]);
        tree.insert_word(vec![1, 2, 3]);
        assert!(tree.contains_word(&[1, 2, 3]));
        assert!(tree.contains_word(&[1, 2]));
        assert_eq!(tree.contains_word(&[]), false);
    }

    #[test]
    fn removal() {
        let mut tree: SearchTrie<u8> = Default::default();
        tree.insert_word(vec![1, 2, 3]);
        tree.insert_word(vec![1, 2]);
        tree.insert_word(vec![2, 2, 3]);
        tree.insert_word(vec![2, 2]);
        tree.remove_word(&[1, 2]);
        assert!(!tree.contains_word(&[1, 2]));
        tree.remove_word(&[1, 2, 3]);
        assert!(!tree.contains_word(&[1, 2, 3]));
        tree.remove_word(&[2, 2, 3]);
        assert!(!tree.contains_word(&[2, 2, 3]));
        tree.remove_word(&[2, 2]);
        assert!(!tree.contains_word(&[3, 2]));
        tree.insert_word(vec![]);
        assert!(tree.contains_word(&[]));
        tree.remove_word(&[]);
        assert!(!tree.contains_word(&[]));
    }

    #[test]
    fn iterators() {
        let mut tree: SearchTrie<u8> = Default::default();
        let mut test_items: Vec<Vec<u8>> = vec![
            vec![1],
            vec![2],
            vec![1, 2, 3, 4],
            vec![1, 2, 2, 4],
            vec![2, 3],
            vec![2, 4],
            vec![1, 4],
            vec![4, 3, 2],
        ];
        for v in test_items.iter().cloned() {
            tree.insert_word(v);
        }
        let mut iter_results: Vec<_> = tree
            .iter()
            .map(|v| v.into_iter().map(|item| *item).collect::<Vec<_>>())
            .collect();
        drop(tree);
        iter_results.sort();
        test_items.sort();
        assert_eq!(test_items, iter_results);
    }
    #[test]
    fn printer() {
        let mut tree: SearchTrie<u8> = Default::default();
        let test_items: Vec<Vec<u8>> = vec![
            vec![1],
            vec![1, 2, 2, 4],
            vec![1, 2, 3, 4],
            vec![1, 4],
            vec![2],
            vec![2, 3],
            vec![2, 4],
            vec![4, 3, 2],
        ];
        for v in test_items.iter().cloned() {
            tree.insert_word(v);
        }
        let s = format!("{}", tree);
        assert_eq!(
            s,
            r#"1!
 2
  2
   4!
  3
   4!
 4!
2!
 3!
 4!
4
 3
  2!
"#
        );
    }
}
