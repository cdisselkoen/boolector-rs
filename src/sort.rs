// We have some methods on `Sort` that we don't use, but still make sense to
// have around for the future
#![allow(dead_code)]

use crate::btor::Btor;
use boolector_sys::*;
use std::borrow::Borrow;

pub struct Sort<R: Borrow<Btor> + Clone> {
    btor: R,
    sort: BoolectorSort,
}

// According to
// https://groups.google.com/forum/#!msg/boolector/itYGgJxU3mY/AC2O0898BAAJ,
// the Boolector library is thread-safe, meaning `BoolectorSort` can be
// both `Send` and `Sync`.
// So as long as `R` is `Send` and/or `Sync`, we can mark `Sort` as `Send`
// and/or `Sync` respectively.
unsafe impl<R: Borrow<Btor> + Clone + Send> Send for Sort<R> {}
unsafe impl<R: Borrow<Btor> + Clone + Sync> Sync for Sort<R> {}

impl<R: Borrow<Btor> + Clone> Sort<R> {
    pub(crate) fn from_raw(btor: R, sort: BoolectorSort) -> Self {
        Self { btor, sort }
    }

    pub(crate) fn as_raw(&self) -> BoolectorSort {
        self.sort
    }

    /// Create a bitvector sort for the given bitwidth.
    /// `width` must not be `0`.
    pub fn bitvector(btor: R, width: u32) -> Self {
        assert!(width > 0, "boolector: cannot create 0-width bitvector sort");
        Self::from_raw(btor.clone(), unsafe {
            boolector_bitvec_sort(btor.borrow().as_raw(), width)
        })
    }

    /// Create the Boolean sort.
    ///
    /// In Boolector, there is no distinction between Booleans and bitvectors of
    /// bitwidth one, so this is equivalent to `Sort::bitvector(btor, 1)`.
    pub fn bool(btor: R) -> Self {
        Self::from_raw(btor.clone(), unsafe {
            boolector_bool_sort(btor.borrow().as_raw())
        })
    }

    /// Create an array sort. An `Array` in Boolector is really just a map
    /// which maps items of the `index` sort to the `element` sort.
    ///
    /// Both the `index` and `element` sorts must be bitvector sorts.
    pub fn array(btor: R, index: &Sort<R>, element: &Sort<R>) -> Self {
        Self::from_raw(btor.clone(), unsafe {
            boolector_array_sort(btor.borrow().as_raw(), index.as_raw(), element.as_raw())
        })
    }

    /// Is `self` an array sort?
    pub fn is_array_sort(&self) -> bool {
        unsafe { boolector_is_array_sort(self.btor.borrow().as_raw(), self.as_raw()) }
    }

    /// Is `self` a bitvector sort?
    pub fn is_bv_sort(&self) -> bool {
        unsafe { boolector_is_bitvec_sort(self.btor.borrow().as_raw(), self.as_raw()) }
    }

    /// Is `self` a function sort?
    pub fn is_fun_sort(&self) -> bool {
        unsafe { boolector_is_fun_sort(self.btor.borrow().as_raw(), self.as_raw()) }
    }
}

impl<R: Borrow<Btor> + Clone> Drop for Sort<R> {
    fn drop(&mut self) {
        unsafe { boolector_release_sort(self.btor.borrow().as_raw(), self.as_raw()) }
    }
}
