// Lean compiler output
// Module: PlaneGraphs.TrivialLowerBound
// Imports: Init PlaneGraphs.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Finset_image___at_PlaneGraphs_starImage___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_PlaneGraphs_starImage___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_image___at_PlaneGraphs_starImage___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1(lean_object*, lean_object*);
lean_object* l_Sym2_instDecidableRel___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1;
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_List_dedup___at_PlaneGraphs_starImage___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_starImage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_PlaneGraphs_starImage___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_dedup___at_PlaneGraphs_starImage___spec__3___boxed(lean_object*, lean_object*);
uint8_t l_List_decidableBAll___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_starSegment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dedup___at_PlaneGraphs_starImage___spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_PlaneGraphs_starImage___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_PlaneGraphs_starImage___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pwFilter___at_PlaneGraphs_starImage___spec__5___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_dedup___at_PlaneGraphs_starImage___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_starSegment(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_starSegment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_mod(x_5, x_4);
lean_dec(x_4);
x_7 = lean_nat_add(x_2, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_starSegment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PlaneGraphs_starSegment(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1;
x_4 = l_Sym2_instDecidableRel___rarg(x_3, x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_instDecidableNot___rarg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_5);
x_11 = l_List_decidableBAll___rarg(x_10, x_5);
if (x_11 == 0)
{
lean_dec(x_9);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_5);
x_3 = x_8;
x_5 = x_13;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_5);
x_11 = l_List_decidableBAll___rarg(x_10, x_5);
if (x_11 == 0)
{
lean_dec(x_9);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_5);
x_3 = x_8;
x_5 = x_13;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_PlaneGraphs_starImage___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_List_redLength___rarg(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l_List_toArrayAux___rarg(x_3, x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_le(x_7, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_7);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_12 = 0;
x_13 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7(x_1, x_6, x_11, x_12, x_2);
lean_dec(x_6);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_7);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 0;
x_18 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8(x_1, x_6, x_16, x_17, x_2);
lean_dec(x_6);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldrTR___at_PlaneGraphs_starImage___spec__6(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_dedup___at_PlaneGraphs_starImage___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_dedup___at_PlaneGraphs_starImage___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_PlaneGraphs_starImage___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Finset_image___at_PlaneGraphs_starImage___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Multiset_map___rarg(x_2, x_3);
x_5 = l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_starImage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_PlaneGraphs_starSegment___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Finset_image___at_PlaneGraphs_starImage___spec__1(x_1, x_3, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_PlaneGraphs_starImage___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldrTR___at_PlaneGraphs_starImage___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_pwFilter___at_PlaneGraphs_starImage___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_PlaneGraphs_starImage___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_dedup___at_PlaneGraphs_starImage___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_dedup___at_PlaneGraphs_starImage___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_dedup___at_PlaneGraphs_starImage___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_dedup___at_PlaneGraphs_starImage___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_PlaneGraphs_starImage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_toFinset___at_PlaneGraphs_starImage___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Finset_image___at_PlaneGraphs_starImage___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Finset_image___at_PlaneGraphs_starImage___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_TrivialLowerBound(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1 = _init_l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_PlaneGraphs_starImage___spec__7___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
