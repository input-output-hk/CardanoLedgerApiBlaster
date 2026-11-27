#include <lean/lean.h>

#ifndef _WIN32
#include <signal.h>
#include <stdatomic.h>

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "Termination signal must be lock-free");

static atomic_int received_signal;

static void record_interrupt(int signal_number) {
    atomic_store_explicit(&received_signal, signal_number, memory_order_relaxed);
}
#endif

LEAN_EXPORT lean_obj_res uplc_equiv_install_interrupt_handler(lean_obj_arg world) {
    (void) world;
#ifndef _WIN32
    struct sigaction action = {0};
    action.sa_handler = record_interrupt;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    if (sigaction(SIGINT, &action, NULL) != 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("Could not install SIGINT handler")));
    }
    if (sigaction(SIGTERM, &action, NULL) != 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("Could not install SIGTERM handler")));
    }
#endif
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res uplc_equiv_received_signal(lean_obj_arg world) {
    (void) world;
#ifndef _WIN32
    return lean_io_result_mk_ok(lean_box_uint32(atomic_load_explicit(&received_signal, memory_order_relaxed)));
#else
    return lean_io_result_mk_ok(lean_box_uint32(0));
#endif
}
