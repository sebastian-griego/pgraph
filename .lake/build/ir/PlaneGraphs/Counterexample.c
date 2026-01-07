// Lean compiler output
// Module: PlaneGraphs.Counterexample
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
static lean_object* l_PlaneGraphs_singlePoint___closed__2;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_PlaneGraphs_trianglePoints___closed__1;
LEAN_EXPORT lean_object* l_PlaneGraphs_singlePoint(lean_object*);
static lean_object* l_PlaneGraphs_singlePoint___closed__1;
static lean_object* l_PlaneGraphs_trianglePoints___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_singlePoint___boxed(lean_object*);
static lean_object* l_PlaneGraphs_trianglePoints___closed__2;
LEAN_EXPORT lean_object* l_PlaneGraphs_trianglePoints(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_trianglePoints___boxed(lean_object*);
static lean_object* _init_l_PlaneGraphs_singlePoint___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_singlePoint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PlaneGraphs_singlePoint___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_singlePoint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_singlePoint___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_singlePoint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_singlePoint(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_trianglePoints___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_trianglePoints___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PlaneGraphs_singlePoint___closed__1;
x_2 = l_PlaneGraphs_trianglePoints___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_PlaneGraphs_trianglePoints___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PlaneGraphs_trianglePoints___closed__1;
x_2 = l_PlaneGraphs_singlePoint___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_trianglePoints(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_PlaneGraphs_trianglePoints___closed__2;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_PlaneGraphs_trianglePoints___closed__3;
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = l_PlaneGraphs_singlePoint___closed__2;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_trianglePoints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_trianglePoints(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_Counterexample(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PlaneGraphs_singlePoint___closed__1 = _init_l_PlaneGraphs_singlePoint___closed__1();
lean_mark_persistent(l_PlaneGraphs_singlePoint___closed__1);
l_PlaneGraphs_singlePoint___closed__2 = _init_l_PlaneGraphs_singlePoint___closed__2();
lean_mark_persistent(l_PlaneGraphs_singlePoint___closed__2);
l_PlaneGraphs_trianglePoints___closed__1 = _init_l_PlaneGraphs_trianglePoints___closed__1();
lean_mark_persistent(l_PlaneGraphs_trianglePoints___closed__1);
l_PlaneGraphs_trianglePoints___closed__2 = _init_l_PlaneGraphs_trianglePoints___closed__2();
lean_mark_persistent(l_PlaneGraphs_trianglePoints___closed__2);
l_PlaneGraphs_trianglePoints___closed__3 = _init_l_PlaneGraphs_trianglePoints___closed__3();
lean_mark_persistent(l_PlaneGraphs_trianglePoints___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
