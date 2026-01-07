// Lean compiler output
// Module: PlaneGraphs.Basic
// Imports: Init Mathlib
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
lean_object* l_Fin_succAbove___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_orient(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_crossingGraph___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap(lean_object*);
lean_object* l_Prod_map___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_HullSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_crossingGraph(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_succAbove___rarg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_HullSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_orient___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_HullSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_HullSize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PlaneGraphs_HullSize(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Fin_succAbove___rarg(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PlaneGraphs_deletePoint___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PlaneGraphs_deletePoint___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_deletePoint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_deletePoint(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Fin_succAbove___rarg___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_3);
x_4 = l_Prod_map___rarg(x_3, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PlaneGraphs_segmentMap___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_segmentMap(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_orient(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_int_sub(x_4, x_5);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_int_sub(x_7, x_8);
x_10 = lean_int_mul(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_int_sub(x_11, x_8);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_int_sub(x_13, x_5);
x_15 = lean_int_mul(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = lean_int_sub(x_10, x_15);
lean_dec(x_15);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_orient___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PlaneGraphs_orient(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_crossingGraph(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_crossingGraph___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PlaneGraphs_crossingGraph(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
