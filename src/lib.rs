extern crate slab;

use ::std::marker::PhantomData;
use ::std::convert::From;
use ::std::ops::{Index, IndexMut};
use ::std::fmt;

#[derive(Clone)]
pub struct Slab<K: Into<usize> + From<usize>, V> {
    inner: slab::Slab<V>,
    _pd: PhantomData<K>,
}

impl<K: Into<usize> + From<usize>, V> Slab<K,V> {
    pub fn new() -> Slab<K, V> {
        Slab {
            inner: slab::Slab::new(),
            _pd: Default::default(),
        }
    }
    pub fn with_capacity(capacity: usize) -> Slab<K, V> {
        Slab {
            inner: slab::Slab::with_capacity(capacity),
            _pd: Default::default(),
        }
    }
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }
    pub fn clear(&mut self) {
        self.inner.clear()
    }
    pub fn len(&self) -> usize {
        self.inner.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
    pub fn iter(&self) -> Iter<K,V> {
        Iter {
            inner: self.inner.iter(),
            _pd: Default::default(),
        }
    }
    pub fn iter_mut(&mut self) -> IterMut<K,V> {
        IterMut {
            inner: self.inner.iter_mut(),
            _pd: Default::default(),
        }
    }
    pub fn get(&self, key: K) -> Option<&V> {
        self.inner.get(key.into())
    }
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.inner.get_mut(key.into())
    }
    pub unsafe fn get_unchecked(&self, key: usize) -> &V {
        self.inner.get_unchecked(key.into())
    }
    pub unsafe fn get_unchecked_mut(&mut self, key: usize) -> &mut V {
        self.inner.get_unchecked_mut(key.into())
    }
    pub fn insert(&mut self, val: V) -> K {
        From::from(self.inner.insert(val))
    }
    pub fn vacant_entry(&mut self) -> VacantEntry<K,V> {
        VacantEntry {
            inner: self.inner.vacant_entry(),
            _pd: Default::default(),
        }
    } 
    pub fn remove(&mut self, key: K) -> V {
        self.inner.remove(key.into())
    }
    pub fn try_remove(&mut self, key: K) -> Option<V> {
        let k = key.into();
        if self.inner.contains(k) {
            Some(self.inner.remove(k))
        } else {
            None
        }
    }
    pub fn contains(&self, key: K) -> bool {
        self.inner.contains(key.into())
    }
    pub fn retain<F>(&mut self, mut f: F) where
            F: FnMut(K, &mut V) -> bool {
        self.inner.retain(|k,v| f(From::from(k),v))
    }
}

#[derive(Debug)]
pub struct Iter<'a, K: Into<usize> + From<usize>, V: 'a> {
    inner: slab::Iter<'a, V>,
    _pd: PhantomData<K>,
}
impl<'a, K: Into<usize> + From<usize>, V> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<(K, &'a V)> {
        self.inner.next().map(|(k,v)|(From::from(k),v))
    }
}

impl<'a, K: Into<usize> + From<usize>, V> IntoIterator for &'a Slab<K,V> {
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> {
        Iter {
            inner: self.inner.iter(),
            _pd: Default::default(),
        }
    }
}



/// An iterator over the key-value pairs of a map, with the
/// values being mutable.
pub struct IterMut<'a, K: Into<usize> + From<usize>, V: 'a> {
    inner: slab::IterMut<'a, V>,
    _pd: PhantomData<K>,
}
impl<'a, K: Into<usize> + From<usize>, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    fn next<'b>(&'b mut self) -> Option<(K, &'a mut V)> {
        self.inner.next().map(|(k,v)|(From::from(k),v))
    }
}


impl<'a, K: Into<usize> + From<usize>, V: 'a> IntoIterator for &'a mut Slab<K, V> {
    type Item = (K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> {
        IterMut {
            inner: self.inner.iter_mut(),
            _pd: Default::default(),
        }
    }
}


#[derive(Debug)]
pub struct VacantEntry<'a, K: Into<usize> + From<usize>, V: 'a> {
    inner: slab::VacantEntry<'a, V>,
    _pd: PhantomData<K>,
}

impl<'a, K: Into<usize> + From<usize>, V : 'a>  VacantEntry<'a, K, V> {
    pub fn insert(self, val: V) -> &'a mut V {
        self.inner.insert(val)
    }
    pub fn key(&self) -> K {
        self.inner.key().into()
    }
}


impl<K:Into<usize> + From<usize>, V: fmt::Debug> fmt::Debug for Slab<K,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}


impl<V,K:Into<usize> + From<usize>> Index<K> for Slab<K,V> {
    type Output = V;
    #[inline]
    fn index(&self, i: K) -> &V {
        self.inner.index(i.into())
    }
}
impl<'a,K:Copy + Into<usize> + From<usize>, V> Index<&'a K> for Slab<K,V> {
    type Output = V;
    fn index(&self, i: &K) -> &V {
        let idx : usize = (*i).into();
        self.inner.index(idx)
    }
}
impl<K:Into<usize> + From<usize>,V> IndexMut<K> for Slab<K,V> {
    fn index_mut(&mut self, i: K) -> &mut V {
        self.inner.index_mut(i.into())
    }
}
impl<'a,K:Copy + Into<usize> + From<usize>, V> IndexMut<&'a K> for Slab<K,V> {
    fn index_mut(&mut self, i: &K) -> &mut V {
        let idx : usize = (*i).into();
        self.inner.index_mut(idx)
    }
}
