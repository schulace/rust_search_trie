use search_trie::SearchTrie;
fn main() {
    let mut t: SearchTrie<char> = SearchTrie::new();
    t.extend(vec!["hello", "hell", "world"].iter().map(|e| e.chars()));
    t.insert_word("help".chars());
    println!("{}", t);
}
