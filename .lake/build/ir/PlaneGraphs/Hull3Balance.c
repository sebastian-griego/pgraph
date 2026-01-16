// Lean compiler output
// Module: PlaneGraphs.Hull3Balance
// Imports: Init PlaneGraphs.Basic PlaneGraphs.Charging PlaneGraphs.DegreeCounts PlaneGraphs.DegreeVectors PlaneGraphs.Asymptotic
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
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__a6;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__c5;
lean_object* l_Nat_cast___at_Rat_instOfNat___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__c4;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__a3;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__c6;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__c3;
static lean_object* l_PlaneGraphs_deg56__n12__a3___closed__1;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__a4;
LEAN_EXPORT lean_object* l_PlaneGraphs_deg56__n12__a5;
static lean_object* _init_l_PlaneGraphs_deg56__n12__a3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at_Rat_instOfNat___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__a3() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__a4() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__a5() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__a6() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__c3() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__c4() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__c5() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
static lean_object* _init_l_PlaneGraphs_deg56__n12__c6() {
_start:
{
lean_object* x_1; 
x_1 = l_PlaneGraphs_deg56__n12__a3___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Charging(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_DegreeCounts(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_DegreeVectors(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Asymptotic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlaneGraphs_Hull3Balance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Charging(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_DegreeCounts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_DegreeVectors(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlaneGraphs_Asymptotic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PlaneGraphs_deg56__n12__a3___closed__1 = _init_l_PlaneGraphs_deg56__n12__a3___closed__1();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__a3___closed__1);
l_PlaneGraphs_deg56__n12__a3 = _init_l_PlaneGraphs_deg56__n12__a3();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__a3);
l_PlaneGraphs_deg56__n12__a4 = _init_l_PlaneGraphs_deg56__n12__a4();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__a4);
l_PlaneGraphs_deg56__n12__a5 = _init_l_PlaneGraphs_deg56__n12__a5();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__a5);
l_PlaneGraphs_deg56__n12__a6 = _init_l_PlaneGraphs_deg56__n12__a6();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__a6);
l_PlaneGraphs_deg56__n12__c3 = _init_l_PlaneGraphs_deg56__n12__c3();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__c3);
l_PlaneGraphs_deg56__n12__c4 = _init_l_PlaneGraphs_deg56__n12__c4();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__c4);
l_PlaneGraphs_deg56__n12__c5 = _init_l_PlaneGraphs_deg56__n12__c5();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__c5);
l_PlaneGraphs_deg56__n12__c6 = _init_l_PlaneGraphs_deg56__n12__c6();
lean_mark_persistent(l_PlaneGraphs_deg56__n12__c6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
