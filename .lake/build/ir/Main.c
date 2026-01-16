// Lean compiler output
// Module: Main
// Imports: Init PlaneGraphs.Asymptotic PlaneGraphs.Charging PlaneGraphs.Counterexample PlaneGraphs.Hull3Balance
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
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg56__sample__main;
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg56__shift__sample__main;
lean_object* l_Nat_cast___at_Rat_instOfNat___spec__1(lean_object*);
extern lean_object* l_PlaneGraphs_K__deg56__sample;
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg34__cert;
extern lean_object* l_PlaneGraphs_K__deg56__shift__sample;
extern lean_object* l_PlaneGraphs_K__deg56__n12__sample;
extern lean_object* l_PlaneGraphs_exampleCertificate;
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg56__n15__sample__main;
static lean_object* l_PlaneGraphs_K__deg34__cert___closed__2;
LEAN_EXPORT lean_object* l_PlaneGraphs_H;
static lean_object* l_PlaneGraphs_K__deg34__cert___closed__4;
LEAN_EXPORT lean_object* l_PlaneGraphs_K__deg56__n12__sample__main;
lean_object* l_PlaneGraphs_Certificate_getQ_x3f(lean_object*, lean_object*);
static lean_object* l_PlaneGraphs_K__deg34__cert___closed__1;
static lean_object* l_PlaneGraphs_K__deg34__cert___closed__3;
extern lean_object* l_PlaneGraphs_K__deg56__n15__sample;
static lean_object* _init_l_PlaneGraphs_H() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__cert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("K_deg34", 7);
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__cert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PlaneGraphs_exampleCertificate;
x_2 = l_PlaneGraphs_K__deg34__cert___closed__1;
x_3 = l_PlaneGraphs_Certificate_getQ_x3f(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__cert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__cert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg34__cert___closed__2;
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_PlaneGraphs_K__deg34__cert___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
static lean_object* _init_l_PlaneGraphs_K__deg34__cert() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg34__cert___closed__4;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg56__sample__main() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg56__sample;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg56__shift__sample__main() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg56__shift__sample;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg56__n12__sample__main() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg56__n12__sample;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_K__deg56__n15__sample__main() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_K__deg56__n15__sample;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Asymptotic(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Charging(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Counterexample(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Hull3Balance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Asymptotic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Charging(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Counterexample(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Hull3Balance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PlaneGraphs_H = _init_l_PlaneGraphs_H();
lean_mark_persistent(l_PlaneGraphs_H);
l_PlaneGraphs_K__deg34__cert___closed__1 = _init_l_PlaneGraphs_K__deg34__cert___closed__1();
lean_mark_persistent(l_PlaneGraphs_K__deg34__cert___closed__1);
l_PlaneGraphs_K__deg34__cert___closed__2 = _init_l_PlaneGraphs_K__deg34__cert___closed__2();
lean_mark_persistent(l_PlaneGraphs_K__deg34__cert___closed__2);
l_PlaneGraphs_K__deg34__cert___closed__3 = _init_l_PlaneGraphs_K__deg34__cert___closed__3();
lean_mark_persistent(l_PlaneGraphs_K__deg34__cert___closed__3);
l_PlaneGraphs_K__deg34__cert___closed__4 = _init_l_PlaneGraphs_K__deg34__cert___closed__4();
lean_mark_persistent(l_PlaneGraphs_K__deg34__cert___closed__4);
l_PlaneGraphs_K__deg34__cert = _init_l_PlaneGraphs_K__deg34__cert();
lean_mark_persistent(l_PlaneGraphs_K__deg34__cert);
l_PlaneGraphs_K__deg56__sample__main = _init_l_PlaneGraphs_K__deg56__sample__main();
lean_mark_persistent(l_PlaneGraphs_K__deg56__sample__main);
l_PlaneGraphs_K__deg56__shift__sample__main = _init_l_PlaneGraphs_K__deg56__shift__sample__main();
lean_mark_persistent(l_PlaneGraphs_K__deg56__shift__sample__main);
l_PlaneGraphs_K__deg56__n12__sample__main = _init_l_PlaneGraphs_K__deg56__n12__sample__main();
lean_mark_persistent(l_PlaneGraphs_K__deg56__n12__sample__main);
l_PlaneGraphs_K__deg56__n15__sample__main = _init_l_PlaneGraphs_K__deg56__n15__sample__main();
lean_mark_persistent(l_PlaneGraphs_K__deg56__n15__sample__main);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
