#include "exception.h"
#include "assert.h"
#include "csr.h"

//-----------------------------------------------------------------
// Defines:
//-----------------------------------------------------------------
#define SR_MPP_SHIFT    11
#define SR_MPP_MASK     0x3
#define SR_MPP          (SR_MPP_MASK  << SR_MPP_SHIFT)
#define SR_MPP_M        (3 << SR_MPP_SHIFT)

//-----------------------------------------------------------------
// exception_handler:
//-----------------------------------------------------------------
struct irq_context * exception_handler(struct irq_context *ctx)
{
    // Timer interrupt
    if (ctx->cause == (CAUSE_INTERRUPT + IRQ_M_TIMER))
    {
        ctx = _timer_handler(ctx);
    }
    // External interrupt
    else if (ctx->cause & CAUSE_INTERRUPT)
    {
        ctx = _irq_handler(ctx);
        /*
        if (_irq_handler)
            
        else
            printf("Unhandled IRQ!\n");
        */
    }
    // Exception
    else
    {
        switch (ctx->cause)
        {
            case CAUSE_ECALL_U:
            case CAUSE_ECALL_S:
            case CAUSE_ECALL_M:
                ctx->pc += 4;
                break;
        }
    }

    return ctx;
}