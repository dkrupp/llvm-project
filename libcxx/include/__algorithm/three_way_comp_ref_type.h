//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef _LIBCPP___ALGORITHM_THREE_WAY_COMP_REF_TYPE_H
#define _LIBCPP___ALGORITHM_THREE_WAY_COMP_REF_TYPE_H

#include <__compare/ordering.h>
#include <__config>
#include <__debug>
#include <__utility/declval.h>

#if !defined(_LIBCPP_HAS_NO_PRAGMA_SYSTEM_HEADER)
#  pragma GCC system_header
#endif

_LIBCPP_BEGIN_NAMESPACE_STD

#if _LIBCPP_STD_VER > 17

template <class _Comp>
struct __debug_three_way_comp {
  _Comp& __comp_;
  _LIBCPP_HIDE_FROM_ABI constexpr __debug_three_way_comp(_Comp& __c) : __comp_(__c) {}

  template <class _Tp, class _Up>
  _LIBCPP_HIDE_FROM_ABI constexpr auto operator()(_Tp& __x, _Up& __y) {
    auto __r = __comp_(__x, __y);
    __do_compare_assert(0, __y, __x, __r);
    return __r;
  }

  template <class _LHS, class _RHS, class _Order>
  _LIBCPP_HIDE_FROM_ABI constexpr inline void __do_compare_assert(int, _LHS& __l, _RHS& __r, _Order __o)
    requires __comparison_category<decltype(std::declval<_Comp&>()(std::declval<_LHS&>(), std::declval<_RHS&>()))>
  {
    _Order __expected = __o;
    if (__o == _Order::less)
      __expected = _Order::greater;
    if (__o == _Order::greater)
      __expected = _Order::less;
    _LIBCPP_DEBUG_ASSERT(__comp_(__l, __r) == __expected, "Comparator does not induce a strict weak ordering");
    (void)__l;
    (void)__r;
    (void)__expected;
  }

  template <class _LHS, class _RHS, class _Order>
  _LIBCPP_HIDE_FROM_ABI constexpr inline void __do_compare_assert(long, _LHS&, _RHS&, _Order) {}
};

// Pass the comparator by lvalue reference. Or in debug mode, using a
// debugging wrapper that stores a reference.
#  ifndef _LIBCPP_ENABLE_DEBUG_MODE
template <class _Comp>
using __three_way_comp_ref_type = __debug_three_way_comp<_Comp>;
#  else
template <class _Comp>
using __three_way_comp_ref_type = _Comp&;
#  endif

#endif // _LIBCPP_STD_VER > 17

_LIBCPP_END_NAMESPACE_STD

#endif // _LIBCPP___ALGORITHM_THREE_WAY_COMP_REF_TYPE_H
