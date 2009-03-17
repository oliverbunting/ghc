/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 2006
 *
 * Debug tracing.  
 *
 * This is a layer over RtsMessages, which provides for generating
 * trace messages with timestamps and task IDs attached
 * automatically.  Also, multiple classes of messages are supported,
 * which can be enabled separately via RTS flags.
 *
 * All debug trace messages go through here.
 *
 * ---------------------------------------------------------------------------*/

#ifndef TRACE_H
#define TRACE_H

// -----------------------------------------------------------------------------
// Tracing functions
// -----------------------------------------------------------------------------

#ifdef DEBUG

void initTracing (void);

// The simple way:
void trace (StgWord32 class, const char *str, ...)
    GNUC3_ATTRIBUTE(format (printf, 2, 3));

// The harder way: sometimes we want to generate a trace message that
// consists of multiple components generated by different functions.
// So we provide the functionality of trace() split into 3 parts: 
//   - traceClass(): a check that the required class is enabled
//   - traceBegin(): print the beginning of the trace message
//   - traceEnd(): complete the trace message (release the lock too).
// 
INLINE_HEADER rtsBool traceClass (StgWord32 class);

void traceBegin (const char *str, ...)
    GNUC3_ATTRIBUTE(format (printf, 1, 2));

void traceEnd (void);

#define debugTrace(class, str, ...) trace(class,str, ## __VA_ARGS__)
// variable arg macros are C99, and supported by gcc.
#define debugTraceBegin(str, ...) traceBegin(str, ## __VA_ARGS__)
#define debugTraceEnd() traceEnd()

#else /* !DEBUG */

#define debugTrace(class, str, ...) /* nothing */
#define debugTraceBegin(str, ...) /* nothing */
#define debugTraceEnd() /* nothing */

#endif

// -----------------------------------------------------------------------------
// Message classes, these may be OR-ed together
// -----------------------------------------------------------------------------

// debugging flags, set with +RTS -D<something>
#define DEBUG_sched		   (1<<0)
#define DEBUG_interp		   (1<<1)
#define DEBUG_weak		   (1<<2)
#define DEBUG_gccafs		   (1<<3) 
#define DEBUG_gc		   (1<<4) 
#define DEBUG_block_alloc	   (1<<5) 
#define DEBUG_sanity		   (1<<6) 
#define DEBUG_stable		   (1<<7) 
#define DEBUG_stm   		   (1<<8) 
#define DEBUG_prof		   (1<<9) 
#define DEBUG_gran		   (1<<10)
#define DEBUG_par		   (1<<11)
#define DEBUG_linker		   (1<<12)
#define DEBUG_squeeze              (1<<13)
#define DEBUG_hpc                  (1<<14)
#define DEBUG_eventlog		   (1<<15)

// -----------------------------------------------------------------------------
// PRIVATE below here
// -----------------------------------------------------------------------------

extern StgWord32 classes_enabled;

INLINE_HEADER rtsBool
traceClass (StgWord32 class) { return (classes_enabled & class); }

// -----------------------------------------------------------------------------

#endif /* TRACE_H */
