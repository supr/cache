use std::borrow::Borrow;
use std::cmp::{Eq, PartialEq};
use std::collections::HashMap;
use std::hash::Hash;
use std::thread;
use std::time::{Duration, Instant};

struct TTLCache<K, V> {
    cache: HashMap<K, (Instant, V)>,
}

impl<K, V> TTLCache<K, V> {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }
}

impl<K, V> TTLCache<K, V>
where
    K: Eq + PartialEq + Hash,
{
    fn has<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.cache.contains_key(key)
    }

    fn insert(&mut self, key: K, v: V, ttl: Duration) -> Option<V> {
        let now = Instant::now();
        if self.has(&key) {
            let old = self.cache.insert(key, (now + ttl, v)).unwrap();
            if now < old.0 {
                return Some(old.1);
            } else {
                return None;
            }
        } else {
            self.cache.insert(key, (now + ttl, v));
            None
        }
    }

    fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let now = Instant::now();
        if let Some(ref v) = self.cache.get(key) {
            if now < v.0 {
                return Some(&v.1);
            }
        }
        None
    }

    fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let now = Instant::now();
        if let Some(v) = self.cache.get(key) {
            if now < v.0 {
                return Some(&mut self.cache.get_mut(key).unwrap().1);
            }
            self.cache.remove_entry(key);
        }
        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        assert_eq!(false, c.has(key));
    }

    #[test]
    fn test_insert() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(key, "foo".as_bytes().to_vec(), Duration::from_secs(10));

        assert_eq!(true, c.has("bar"));
    }

    #[test]
    fn text_expire() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(key, "foo".as_bytes().to_vec(), Duration::from_micros(500));
        assert_eq!(true, c.has("bar"));
        thread::sleep(Duration::from_secs(1));
        assert_eq!(None, c.get("bar"));
    }

    #[test]
    fn test_mutate() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(key, "foo".as_bytes().to_vec(), Duration::from_secs(10));
        if let Some(val) = c.get_mut("bar") {
            val.push('b' as u8);
            val.push('a' as u8);
            val.push('r' as u8);
        }
        assert_eq!(Some(&"foobar".as_bytes().to_vec()), c.get("bar"))
    }
}
