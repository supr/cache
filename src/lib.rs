use std::borrow::Borrow;
use std::cmp::{Eq, PartialEq};
use std::collections::HashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

pub struct TTLCache<K, V> {
    cache: HashMap<K, (Option<Instant>, V)>,
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
    fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.cache.contains_key(key)
    }

    /// Insert a key value pair into the underlying cache, with an optional expiry.
    ///
    /// 1. If an existing key is already present and the key has not expired, then return old value
    ///    after inserting the new one.
    /// 2. If no existing key is present insert key, value pairs with optional ttl into the cache.
    pub fn insert(&mut self, key: K, v: V, ttl: Option<Duration>) -> Option<V> {
        let now = Instant::now();
        let expiry = ttl.map(|exp| now + exp);
        if let Some(old) = self.cache.insert(key, (expiry, v)) {
            return Some(old.1);
        }
        None
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let now = Instant::now();
        if let Some(ref v) = self.cache.get(key) {
            return v.0.map_or(
                Some(&v.1),
                |inst| {
                    if now < inst {
                        Some(&v.1)
                    } else {
                        None
                    }
                },
            );
        }
        None
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let now = Instant::now();
        if let Some(ref v) = self.cache.get(key) {
            if let Some(inst) = v.0 {
                if now < inst {
                    return Some(&mut self.cache.get_mut(key).unwrap().1);
                }
                self.cache.remove_entry(key);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn it_works() {
        let c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        assert_eq!(false, c.contains_key(key));
    }

    #[test]
    fn test_insert() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(
            key,
            "foo".as_bytes().to_vec(),
            Some(Duration::from_secs(10)),
        );

        assert_eq!(true, c.contains_key("bar"));
    }

    #[test]
    fn text_expire() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(
            key,
            "foo".as_bytes().to_vec(),
            Some(Duration::from_micros(500)),
        );
        assert_eq!(true, c.contains_key("bar"));
        thread::sleep(Duration::from_secs(1));
        assert_eq!(None, c.get("bar"));
    }

    #[test]
    fn test_mutate() {
        let mut c: TTLCache<&str, Vec<u8>> = TTLCache::new();
        let key = "bar";

        c.insert(
            key,
            "foo".as_bytes().to_vec(),
            Some(Duration::from_secs(10)),
        );
        if let Some(val) = c.get_mut("bar") {
            val.push('b' as u8);
            val.push('a' as u8);
            val.push('r' as u8);
        }
        assert_eq!(Some(&"foobar".as_bytes().to_vec()), c.get("bar"))
    }
}
