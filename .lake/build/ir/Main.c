// Lean compiler output
// Module: Main
// Imports: Init PlaneGraphs.Asymptotic PlaneGraphs.Charging PlaneGraphs.Counterexample
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
LEAN_EXPORT lean_object* l_PlaneGraphs_H;
static lean_object* _init_l_PlaneGraphs_H() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Asymptotic(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Charging(uint8_t builtin, lean_object*);
lean_object* initialize_PlaneGraphs_Counterexample(uint8_t builtin, lean_object*);
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
l_PlaneGraphs_H = _init_l_PlaneGraphs_H();
lean_mark_persistent(l_PlaneGraphs_H);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
