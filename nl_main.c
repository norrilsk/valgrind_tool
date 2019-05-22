
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)

static Bool nl_process_cmd_line_option(const HChar* arg)
{
   return True;
}

static void nl_print_usage(void)
{  
   VG_(printf)(
"    (none)\n"
   );
}

static void nl_print_debug_usage(void)
{  
   VG_(printf)(
"    (none)\n"
   );
}


/* Nb: use ULongs because the numbers can get very big */

static ULong n_SBs_entered   = 0;
static ULong n_SBs_completed = 0;
static ULong n_IRStmts       = 0;

static void add_one_SB_entered(void)
{
   n_SBs_entered++;
}


static void add_one_SB_completed(void)
{
   n_SBs_completed++;
}

static void add_one_IRStmt(void)
{
   n_IRStmts++;
}

static ULong n_guest_instrs  = 0;

static void add_n_guest_instr(int n)
{
   n_guest_instrs+=n;
}

static ULong n_Jccs = 0;
static ULong n_Jccs_untaken = 0;
static ULong n_IJccs = 0;
static ULong n_IJccs_untaken = 0;
static void add_one_Jcc(void)
{
   n_Jccs++;
}

static void add_one_Jcc_untaken(void)
{
   n_Jccs_untaken++;
}
static ULong total_jc = 0;
static void add_total(void)
{
	total_jc++;
}
static void add_one_inverted_Jcc(void)
{
   n_IJccs++;
}

static void add_one_inverted_Jcc_untaken(void)
{
   n_IJccs_untaken++;
}

static void nl_post_clo_init(void)
{
}

static
IRSB* nl_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn, 
                      const VexGuestLayout* layout, 
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   IRDirty*   di;
   Int        i;
   IRSB*      sbOut;
   Addr       iaddr = 0, dst;
   UInt       ilen = 0;
   Bool       condition_inverted = False;
   /* Set up SB */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   // Copy verbatim any IR preamble preceding the first IMark
   i = 0;
   while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      if (sbIn->stmts[i]->tag != Ist_NoOp)
          addStmtToIRSB( sbOut, sbIn->stmts[i] );
      i++;
   }
   di = unsafeIRDirty_0_N( 0, "add_one_SB_entered",
                           VG_(fnptr_to_fnentry)( &add_one_SB_entered ),
                           mkIRExprVec_0() );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   
   HWord gcnt = 0;
   HWord stat = 0;
   IRExpr *arg1, **argv;
   for (/*use current i*/; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st || st->tag == Ist_NoOp) continue;
      di = unsafeIRDirty_0_N( 0, "add_one_IRStmt",
                              VG_(fnptr_to_fnentry)( &add_one_IRStmt ),
                              mkIRExprVec_0() );
      addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
      switch (st->tag) {
         case Ist_IMark:
   
            /* Needed to be able to check for inverted condition in Ist_Exit */
            iaddr = st->Ist.IMark.addr;
            ilen  = st->Ist.IMark.len;
            
            /* Count guest instruction. */
            gcnt++;
            break;
         case Ist_LoadG:
         {
             IRLoadG *lg = st->Ist.LoadG.details;
             IRType type = Ity_INVALID;
             IRType typeWide = Ity_INVALID;
             typeOfIRLoadGOp(lg->cvt, &typeWide, &type);
             if (type == Ity_I32)
             {
                 stat++;
             }
             break;
         }
	   
         case Ist_Exit:
         {
    
             tl_assert(iaddr != 0);
             dst = (sizeof(Addr) == 4) ? st->Ist.Exit.dst->Ico.U32 :
                   st->Ist.Exit.dst->Ico.U64;
    
             condition_inverted = (dst == iaddr + ilen);
             if (!condition_inverted)
             {
                 di = unsafeIRDirty_0_N(0, "add_one_Jcc",
                                        VG_(fnptr_to_fnentry)(&add_one_Jcc),
                                        mkIRExprVec_0());
             }
             else
             {
                 di = unsafeIRDirty_0_N(0, "add_one_inverted_Jcc",
                                        VG_(fnptr_to_fnentry)(
                                            &add_one_inverted_Jcc),
                                        mkIRExprVec_0());
             }
             addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
             addStmtToIRSB( sbOut, st );
	     di = unsafeIRDirty_0_N(0, "add_total",
                                        VG_(fnptr_to_fnentry)(
                                            &add_total),
                                        mkIRExprVec_0());

             addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
             addStmtToIRSB( sbOut, st );

             /* Count non-taken Jcc */
             if (!condition_inverted)
             {
                 di = unsafeIRDirty_0_N(0, "add_one_Jcc_untaken",
                                        VG_(fnptr_to_fnentry)(
                                            &add_one_Jcc_untaken),
                                        mkIRExprVec_0());
             }
             else
             {
                 di = unsafeIRDirty_0_N(0, "add_one_inverted_Jcc_untaken",
                                        VG_(fnptr_to_fnentry)(
                                            &add_one_inverted_Jcc_untaken),
                                        mkIRExprVec_0());
             }
             addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
             arg1 = mkIRExpr_HWord(gcnt);
             argv = mkIRExprVec_1(arg1);
    
             di = unsafeIRDirty_0_N(1, "add_n_guest_instr",
                                    VG_(fnptr_to_fnentry)(&add_n_guest_instr),
                                    argv);
             addStmtToIRSB(sbOut, IRStmt_Dirty(di));
             stat = 0;
             gcnt = 0;
             break;
         }
         default:
            break;
      }

      addStmtToIRSB( sbOut, st );
   }
   di = unsafeIRDirty_0_N( 0, "add_one_SB_completed",
                           VG_(fnptr_to_fnentry)( &add_one_SB_completed ),
                           mkIRExprVec_0() );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   
   if (gcnt != 0)
   {
      arg1 = mkIRExpr_HWord( gcnt );
      argv = mkIRExprVec_1(arg1);

      di = unsafeIRDirty_0_N( 1, "add_n_guest_instr",
       		                   VG_(fnptr_to_fnentry)( &add_n_guest_instr ),
       		                   argv);
      addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   }

   return sbOut;
}

static void nl_fini(Int exitcode)
{
   ULong total_Jccs = n_Jccs + n_IJccs;
   ULong taken_Jccs = (n_Jccs - n_Jccs_untaken) + n_IJccs_untaken;
   
   VG_(umsg)("\n");
   VG_(umsg)("Executed:\n");
   VG_(umsg)("  SBs entered:  %'llu\n", n_SBs_entered);
   VG_(umsg)("  SBs completed:  %'llu\n", n_SBs_completed);
   VG_(umsg)("  n IRStmts:  %'llu\n", n_IRStmts);
   VG_(umsg)("  n guest instr:  %'llu\n", n_guest_instrs);
   VG_(umsg)("  n total:  %'llu\n", n_guest_instrs);
   VG_(umsg)("  n total jccs old:  %'llu\n", total_Jccs);
   VG_(umsg)("  total Jccs:  %'llu\n", total_jc);
   VG_(umsg)("  taken Jccs:  %'llu\n", taken_Jccs);
   VG_(umsg)("\n");
   VG_(umsg)("Exit code:       %d\n", exitcode);
}

static void nl_pre_clo_init(void)
{
   VG_(details_name)            ("Icount");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("an example Valgrind tool which counts guest instructions");
   VG_(details_copyright_author)(
      "Copyright (C) 2002-2015, and GNU GPL'd, by IamIntel.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);
   VG_(details_avg_translation_sizeB) ( 200 );

   VG_(basic_tool_funcs)          (nl_post_clo_init,
                                   nl_instrument,
                                   nl_fini);
   VG_(needs_command_line_options)(nl_process_cmd_line_option,
                                   nl_print_usage,
                                   nl_print_debug_usage);
}

VG_DETERMINE_INTERFACE_VERSION(nl_pre_clo_init)
