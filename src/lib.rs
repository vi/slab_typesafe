//! A type-safe wrapper for [slab](../slab/index.html).
//! It implements the same data structure with the same methods,
//! but takes and returns special tokens instead of `usize` values,
//! preventing you from confusing them with other unrelated `usize`s,
//! including keys for other Slab instances.
//!
//! Based on [compactmap::wrapped](https://docs.rs/compactmap/0.3.4/compactmap/wrapped/index.html)
//!
//! # Examples
//!
//! Basic storing and retrieval.
//!
//! ```
//! #[macro_use] 
//! extern crate slab_typesafe;
//! # use slab_typesafe::*;
//! declare_slab_token!(StringHandle);
//! # fn main(){
//! let mut slab : Slab<StringHandle, &'static str> = Slab::new();
//!
//! let hello = slab.insert("hello");
//! let world = slab.insert("world");
//!
//! assert_eq!(slab[hello], "hello");
//! assert_eq!(slab[world], "world");
//!
//! slab[world] = "earth";
//! assert_eq!(slab[world], "earth");
//! # }
//! ```
//! 
//! Error if you confused the handles
//!
//! ```compile_fail
//! #[macro_use] 
//! extern crate slab_typesafe;
//! # use slab_typesafe::*;
//! declare_slab_token!(StringHandle1);
//! declare_slab_token!(StringHandle2);
//! # fn main(){
//! let mut slab1 : Slab<StringHandle1, _> = Slab::new();
//! let mut slab2 : Slab<StringHandle2, _> = Slab::new();
//!
//! let hello = slab1.insert("hello");
//! let world = slab2.insert("world");
//!
//! slab1[world]; // the type `Slab<StringHandle1, _>` cannot be indexed by `StringHandle2`
//! slab2.remove(hello); // expected struct `StringHandle2`, found struct `StringHandle1`
//! # }
//! ```
//!
//! See the rest of examples in [the original documentation](../slab/index.html).
//!
//! The documentation is mostly a copy of the original crate's documentation.

extern crate slab;

use ::std::marker::PhantomData;
use ::std::convert::From;
use ::std::ops::{Index, IndexMut};
use ::std::fmt;

/// A wrapper for pre-allocated storage for a uniform data type
///
/// See [module documentation] for more details.
///
/// [module documentation]: index.html
#[derive(Clone)]
pub struct Slab<K: Into<usize> + From<usize>, V> {
    inner: slab::Slab<V>,
    _pd: PhantomData<K>,
}

impl<K: Into<usize> + From<usize>, V> Slab<K,V> {
    /// Construct a new, empty `Slab`.
    ///
    /// The function does not allocate and the returned slab will have no
    /// capacity until `insert` is called or capacity is explicitly reserved.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let slab: Slab<MyIndex, i32> = Slab::new();
    /// # }
    /// ```
    pub fn new() -> Slab<K, V> {
        Slab {
            inner: slab::Slab::new(),
            _pd: Default::default(),
        }
    }
    
    /// Construct a new, empty `Slab` with the specified capacity.
    ///
    /// The returned slab will be able to store exactly `capacity` without
    /// reallocating. If `capacity` is 0, the slab will not allocate.
    ///
    /// It is important to note that this function does not specify the *length*
    /// of the returned slab, but only the capacity. For an explanation of the
    /// difference between length and capacity, see [Capacity and
    /// reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab = Slab::<MyIndex, _>::with_capacity(10);
    ///
    /// // The slab contains no values, even though it has capacity for more
    /// assert_eq!(slab.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     slab.insert(i);
    /// }
    ///
    /// // ...but this may make the slab reallocate
    /// slab.insert(11);
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize) -> Slab<K, V> {
        Slab {
            inner: slab::Slab::with_capacity(capacity),
            _pd: Default::default(),
        }
    }
    
    /// Returns the number of values the slab can store without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let slab: Slab<MyIndex, i32> = Slab::with_capacity(10);
    /// assert_eq!(slab.capacity(), 10);
    /// # }
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserves capacity for at least `additional` more values to be stored
    /// without allocating.
    ///
    /// `reserve` does nothing if the slab already has sufficient capcity for
    /// `additional` more values. If more capacity is required, a new segment of
    /// memory will be allocated and all existing values will be copied into it.
    /// As such, if the slab is already very large, a call to `reserve` can end
    /// up being expensive.
    ///
    /// The slab may reserve more than `additional` extra space in order to
    /// avoid frequent reallocations. Use `reserve_exact` instead to guarantee
    /// that only the requested space is allocated.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    /// slab.insert("hello");
    /// slab.reserve(10);
    /// assert!(slab.capacity() >= 11);
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Reserves the minimum capacity required to store exactly `additional`
    /// more values.
    ///
    /// `reserve_exact` does nothing if the slab already has sufficient capacity
    /// for `additional` more valus. If more capacity is required, a new segment
    /// of memory will be allocated and all existing values will be copied into
    /// it.  As such, if the slab is already very large, a call to `reserve` can
    /// end up being expensive.
    ///
    /// Note that the allocator may give the slab more space than it requests.
    /// Therefore capacity can not be relied upon to be precisely minimal.
    /// Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    /// slab.insert("hello");
    /// slab.reserve_exact(10);
    /// assert!(slab.capacity() >= 11);
    /// # }
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }
    
    /// Shrinks the capacity of the slab as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    /// Also, since values are not moved, the slab cannot shrink past any stored
    /// values.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, i32> = Slab::with_capacity(10);
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// assert_eq!(slab.capacity(), 10);
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3);
    /// # }
    /// ```
    ///
    /// In this case, even though two values are removed, the slab cannot shrink
    /// past the last value.
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, i32> = Slab::with_capacity(10);
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.remove(0.into());
    /// slab.remove(1.into());
    ///
    /// assert_eq!(slab.capacity(), 10);
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3);
    /// # }
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }
    
    /// Clear the slab of all values
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.clear();
    /// assert!(slab.is_empty());
    /// # }
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear()
    }
    
    /// Returns the number of stored values
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// assert_eq!(3, slab.len());
    /// # }
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }
    
    /// Returns `true` if no values are stored in the slab
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, usize> = Slab::new();
    /// assert!(slab.is_empty());
    ///
    /// slab.insert(1);
    /// assert!(!slab.is_empty());
    /// # }
    /// ```
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns an iterator over the slab
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vaccant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, u32> = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// let mut iterator = slab.iter();
    ///
    /// assert_eq!(iterator.next(), Some((0.into(), &0)));
    /// assert_eq!(iterator.next(), Some((1.into(), &1)));
    /// assert_eq!(iterator.next(), Some((2.into(), &2)));
    /// assert_eq!(iterator.next(), None);
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<K,V> {
        Iter {
            inner: self.inner.iter(),
            _pd: Default::default(),
        }
    }
    
    /// Returns an iterator that allows modifying each value.
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vaccant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, u32> = Slab::new();
    ///
    /// let key1 = slab.insert(0);
    /// let key2 = slab.insert(1);
    ///
    /// for (key, val) in slab.iter_mut() {
    ///     if key == key1 {
    ///         *val += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 1);
    /// # }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K,V> {
        IterMut {
            inner: self.inner.iter_mut(),
            _pd: Default::default(),
        }
    }
    
    /// Returns a reference to the value associated with the given key
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    /// let key : MyIndex = slab.insert("hello");
    ///
    /// assert_eq!(slab.get(key), Some(&"hello"));
    /// assert_eq!(slab.get(123.into()), None);
    /// # }
    /// ```
    pub fn get(&self, key: K) -> Option<&V> {
        self.inner.get(key.into())
    }
    
    /// Returns a mutable reference to the value associated with the given key
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, &'static str> = Slab::new();
    /// let key : MyIndex = slab.insert("hello");
    ///
    /// *slab.get_mut(key).unwrap() = "world";
    ///
    /// assert_eq!(slab[key], "world");
    /// assert_eq!(slab.get_mut(123.into()), None);
    /// # }
    /// ```
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.inner.get_mut(key.into())
    }
    
    /// Returns a reference to the value associated with the given key without
    /// performing bounds checking.
    ///
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex,_> = Slab::new();
    /// let key : MyIndex = slab.insert(2);
    ///
    /// unsafe {
    ///     assert_eq!(slab.get_unchecked(key), &2);
    /// }
    /// # }
    /// ```
    pub unsafe fn get_unchecked(&self, key: K) -> &V {
        self.inner.get_unchecked(key.into())
    }
    
    /// Returns a mutable reference to the value associated with the given key
    /// without performing bounds checking.
    ///
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab < MyIndex, u16> = Slab::new();
    /// let key = slab.insert(2);
    ///
    /// unsafe {
    ///     let val = slab.get_unchecked_mut(key);
    ///     *val = 13;
    /// }
    ///
    /// assert_eq!(slab[key], 13);
    /// # }
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> &mut V {
        self.inner.get_unchecked_mut(key.into())
    }
    
    /// Insert a value in the slab, returning key assigned to the value
    ///
    /// The returned key can later be used to retrieve or remove the value using indexed
    /// lookup and `remove`. Additional capacity is allocated if needed. See
    /// [Capacity and reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    /// let key : MyIndex = slab.insert("hello");
    /// assert_eq!(slab[key], "hello");
    /// # }
    /// ```
    pub fn insert(&mut self, val: V) -> K {
        From::from(self.inner.insert(val))
    }
    
    /// Returns a handle to a vacant entry allowing for further manipulation.
    ///
    /// This function is useful when creating values that must contain their
    /// slab key. The returned `VaccantEntry` reserves a slot in the slab and is
    /// able to query the associated key.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab  : Slab<MyIndex, _> = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key : MyIndex  = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// # }
    /// ```
    pub fn vacant_entry(&mut self) -> VacantEntry<K,V> {
        VacantEntry {
            inner: self.inner.vacant_entry(),
            _pd: Default::default(),
        }
    } 
    
    /// Removes and returns the value associated with the given key.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not associated with a value.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex,_> = Slab::new();
    ///
    /// let hello : MyIndex = slab.insert("hello");
    ///
    /// assert_eq!(slab.remove(hello), "hello");
    /// assert!(!slab.contains(hello));
    /// # }
    /// ```
    pub fn remove(&mut self, key: K) -> V {
        self.inner.remove(key.into())
    }
    
    /// Removes and returns the value associated with the given key, if it exists.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex,_> = Slab::new();
    ///
    /// let hello : MyIndex = slab.insert("hello");
    ///
    /// assert_eq!(slab.try_remove(hello), Some("hello"));
    /// assert_eq!(slab.try_remove(hello), None);
    /// # }
    /// ```
    pub fn try_remove(&mut self, key: K) -> Option<V> {
        let k = key.into();
        if self.inner.contains(k) {
            Some(self.inner.remove(k))
        } else {
            None
        }
    }
    
    /// Returns `true` if a value is associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex,_> = Slab::new();
    ///
    /// let hello : MyIndex = slab.insert("hello");
    /// assert!(slab.contains(hello));
    ///
    /// slab.remove(hello);
    ///
    /// assert!(!slab.contains(hello));
    /// # }
    /// ```
    pub fn contains(&self, key: K) -> bool {
        self.inner.contains(key.into())
    }
    
    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(usize, &mut e)`
    /// returns false. This method operates in place and preserves the key
    /// associated with the retained values.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    ///
    /// let k1 : MyIndex = slab.insert(0);
    /// let k2 : MyIndex = slab.insert(1);
    /// let k3 : MyIndex = slab.insert(2);
    ///
    /// slab.retain(|key, val| key == k1 || *val == 1);
    ///
    /// assert!(slab.contains(k1));
    /// assert!(slab.contains(k2));
    /// assert!(!slab.contains(k3));
    ///
    /// assert_eq!(2, slab.len());
    /// # }
    /// ```
    pub fn retain<F>(&mut self, mut f: F) where
            F: FnMut(K, &mut V) -> bool {
        self.inner.retain(|k,v| f(From::from(k),v))
    }
}

/// An iterator over the values stored in the `Slab`
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



/// A mutable iterator over the values stored in the `Slab`
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

/// A handle to an vacant entry in a `Slab`.
///
/// `VacantEntry` allows constructing values with the key that they will be
/// assigned to.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate slab_typesafe;
/// declare_slab_token!(MyIndex);
/// # fn main(){
/// # use slab_typesafe::*;
/// let mut slab : Slab<MyIndex, _> = Slab::new();
///
/// let hello = {
///     let entry = slab.vacant_entry();
///     let key = entry.key();
///
///     entry.insert((key, "hello"));
///     key
/// };
///
/// assert_eq!(hello, slab[hello].0);
/// assert_eq!("hello", slab[hello].1);
/// # }
/// ```
#[derive(Debug)]
pub struct VacantEntry<'a, K: Into<usize> + From<usize>, V: 'a> {
    inner: slab::VacantEntry<'a, V>,
    _pd: PhantomData<K>,
}

impl<'a, K: Into<usize> + From<usize>, V : 'a>  VacantEntry<'a, K, V> {
        /// Insert a value in the entry, returning a mutable reference to the value.
    ///
    /// To get the key associated with the value, use `key` prior to calling
    /// `insert`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab<MyIndex, _> = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key : MyIndex = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// # }
    /// ```
    pub fn insert(self, val: V) -> &'a mut V {
        self.inner.insert(val)
    }
    
    /// Return the key associated with this entry.
    ///
    /// A value stored in this entry will be associated with this key.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate slab_typesafe;
    /// declare_slab_token!(MyIndex);
    /// # fn main(){
    /// # use slab_typesafe::*;
    /// let mut slab : Slab <MyIndex, _> = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key : MyIndex = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// # }
    /// ```
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

/// Create usize-equivalent struct that implements `From<usize>` and `Into<usize>`
///
/// You it as a key K for the wrapped [Slab](struct.Slab.html)
///
/// ```
/// #[macro_use] extern crate slab_typesafe;
/// declare_slab_token!(MySpecialIndex);
/// # fn main(){}
/// ```
#[macro_export]
macro_rules! declare_slab_token {
    ($x:ident) => {
        #[derive(Copy,Clone,Ord,PartialOrd,Eq,PartialEq,Hash,Debug)]
        struct $x(usize);
        impl From<usize> for $x {
            fn from(x:usize) -> Self { $x(x) }
        }
        impl From<$x> for usize {
            fn from(x:$x) -> usize {x.0}
        }
    }
}
