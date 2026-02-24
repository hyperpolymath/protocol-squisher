// SPDX-License-Identifier: PMPL-1.0-or-later

use bytemuck::Pod;
use std::borrow::Cow;
use std::mem::{align_of, size_of};

/// Classification for whether a path can remain zero-copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZeroCopyDecision {
    Borrowed,
    RequiresCopy,
}

/// Returns true when two POD types are layout-compatible for cast-based zero-copy.
pub fn is_layout_compatible<T: Pod, U: Pod>() -> bool {
    size_of::<T>() == size_of::<U>() && align_of::<T>() == align_of::<U>()
}

/// Attempt a zero-copy cast over a slice when POD/layout constraints hold.
pub fn try_cast_slice<T: Pod, U: Pod>(input: &[T]) -> Option<&[U]> {
    if !is_layout_compatible::<T, U>() {
        return None;
    }
    bytemuck::try_cast_slice(input).ok()
}

/// Decide if a zero-copy path can be selected for this conversion.
pub fn choose_zero_copy<T: Pod, U: Pod>() -> ZeroCopyDecision {
    if is_layout_compatible::<T, U>() {
        ZeroCopyDecision::Borrowed
    } else {
        ZeroCopyDecision::RequiresCopy
    }
}

/// Return a borrowed cast when possible, otherwise materialize a copied mapping.
pub fn cast_or_map<T, U, F>(input: &[T], map: F) -> Cow<'_, [U]>
where
    T: Pod + Copy,
    U: Pod + Copy,
    F: FnMut(T) -> U,
{
    if let Some(cast) = try_cast_slice::<T, U>(input) {
        Cow::Borrowed(cast)
    } else {
        Cow::Owned(input.iter().copied().map(map).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytemuck::{Pod, Zeroable};

    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Zeroable, Pod)]
    struct A(u32);

    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Zeroable, Pod)]
    struct B(u32);

    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Zeroable, Pod)]
    struct C(u64);

    #[test]
    fn compatible_types_allow_cast() {
        assert!(is_layout_compatible::<A, B>());
        assert_eq!(choose_zero_copy::<A, B>(), ZeroCopyDecision::Borrowed);

        let data = [A(1), A(2), A(3)];
        let casted = try_cast_slice::<A, B>(&data).expect("expected cast");
        assert_eq!(casted.len(), 3);
        assert_eq!(casted[1].0, 2);
    }

    #[test]
    fn incompatible_types_reject_cast() {
        assert!(!is_layout_compatible::<A, C>());
        assert_eq!(choose_zero_copy::<A, C>(), ZeroCopyDecision::RequiresCopy);
        let data = [A(1), A(2)];
        assert!(try_cast_slice::<A, C>(&data).is_none());
    }

    #[test]
    fn cast_or_map_falls_back_to_copy() {
        let data = [A(1), A(2), A(3)];
        let mapped = cast_or_map::<A, C, _>(&data, |a| C(a.0 as u64));
        assert!(matches!(mapped, Cow::Owned(_)));
        assert_eq!(mapped[2].0, 3);
    }
}
