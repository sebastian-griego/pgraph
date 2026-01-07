// Lean compiler output
// Module: PlaneGraphs.Charging
// Imports: Init Mathlib PlaneGraphs.ExpectationLemma PlaneGraphs.Certificate
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
lean_object* l_Nat_cast___at_Rat_instOfNat___spec__1(lean_object*);
static lean_object* l_PlaneGraphs_K__deg34__step___closed__2;
static lean_object* l_PlaneGraphs_K__deg34__step___closed__3;
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
static lean_object* l_PlaneGraphs_K__deg34__step___closed__1;
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg34__step(lean_object*);
static lean_object* _init_l_PlaneGraphs_K__deg34__step___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__step___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__step___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg34__step(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
x_3 = l_PlaneGraphs_K__deg34__step___closed__1;
x_4 = l_Rat_mul(x_3, x_2);
x_5 = l_PlaneGraphs_K__deg34__step___closed__2;
x_6 = l_Rat_mul(x_5, x_2);
lean_dec(x_2);
x_7 = l_PlaneGraphs_K__deg34__step___closed__3;
x_8 = l_Rat_sub(x_6, x_7);
x_9 = l_Rat_div(x_4, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_ExpectationLemma(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Certificate(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_Charging(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_ExpectationLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Certificate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PlaneGraphs_K__deg34__step___closed__1 = _init_l_PlaneGraphs_K__deg34__step___closed__1();
lean_mark_persistent(l_PlaneGraphs_K__deg34__step___closed__1);
l_PlaneGraphs_K__deg34__step___closed__2 = _init_l_PlaneGraphs_K__deg34__step___closed__2();
lean_mark_persistent(l_PlaneGraphs_K__deg34__step___closed__2);
l_PlaneGraphs_K__deg34__step___closed__3 = _init_l_PlaneGraphs_K__deg34__step___closed__3();
lean_mark_persistent(l_PlaneGraphs_K__deg34__step___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
