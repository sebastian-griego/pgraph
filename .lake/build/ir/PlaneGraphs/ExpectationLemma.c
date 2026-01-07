// Lean compiler output
// Module: PlaneGraphs.ExpectationLemma
// Imports: Init Mathlib PlaneGraphs.Basic
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
static lean_object* l_PlaneGraphs_basePointSet___closed__2;
LEAN_EXPORT lean_object* l_PlaneGraphs_basePointSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset___boxed(lean_object*);
lean_object* l_PlaneGraphs_segmentMap___rarg(lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_PlaneGraphs_basePointSet___closed__1;
LEAN_EXPORT lean_object* l_PlaneGraphs_basePointSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_PlaneGraphs_segmentMap___rarg), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Multiset_map___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PlaneGraphs_segmentMapFinset___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_segmentMapFinset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_segmentMapFinset(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_basePointSet___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_basePointSet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PlaneGraphs_basePointSet___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_basePointSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PlaneGraphs_basePointSet___closed__2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_basePointSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PlaneGraphs_basePointSet(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_ExpectationLemma(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PlaneGraphs_basePointSet___closed__1 = _init_l_PlaneGraphs_basePointSet___closed__1();
lean_mark_persistent(l_PlaneGraphs_basePointSet___closed__1);
l_PlaneGraphs_basePointSet___closed__2 = _init_l_PlaneGraphs_basePointSet___closed__2();
lean_mark_persistent(l_PlaneGraphs_basePointSet___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
