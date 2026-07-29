/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#ifndef CPROVER_CBMC_CBMC_PARSE_OPTIONS_H
#define CPROVER_CBMC_CBMC_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <functional>

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_trace.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/goto_check_c.h>
#include <goto-checker/bmc_util.h>
#include <goto-instrument/cover.h>
#include <json/json_interface.h>
#include <langapi/language.h>
#include <solvers/strings/string_refinement.h>
#include <xmllang/xml_interface.h>

class optionst;

// clang-format off
#define CBMC_OPTIONS \
  "(deagle-closure)(deagle-icd)(deagle-segment)(deagle-nondet-bulk-init)(native-adaptive-indexed-dispatch)(native-indexed-dispatch)(datarace)(goblint)(locksmith)(deadlock)" \
  "(interference-predicate-self-test)" \
  "(interference-predicate-profile)" \
  "(interference-predicate-fixedpoint)" \
  "(interference-predicate-recursive-worker-fixedpoint)" \
  "(protocol-induced-capacity-cutoff)" \
  "(native-lock-ego-abstraction)" \
  "(native-jces)(native-pure-spin-wait)(native-prefix-affine-envelope)(native-property-affine-audit)(native-property-affine-proof)(native-role-split-stream-audit)(native-publication-frontier-audit)(native-relational-bisimulation-audit)(native-group-action-cancellation-audit)(native-segmented-fold-audit)(native-nested-iteration-audit)(native-local-loop-accel-audit)(native-homogeneous-spawn-witness-audit)(native-homogeneous-spawn-witness)(native-alternating-phase-audit)(native-alternating-phase-recurrence)(native-nonnegative-oscillator-monitor)(native-indexed-lifecycle-audit)(native-indexed-lifecycle-prefix)(native-dormant-spawn-cutoff-audit)(native-dormant-spawn-cutoff)(native-single-worker-initialization-prefix)(native-main-worker-prefix)(native-pair-initialization-prefix)(native-dormant-spawn-pair-audit)(native-dormant-spawn-pair):(native-dormant-spawn-pair-portfolio)(native-counterexample-rescue-portfolio)" \
  OPT_BMC \
  "(preprocess)(slice-by-trace):" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  OPT_REACHABILITY_SLICER \
  "(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(test-preprocessor)" \
  "(show-array-constraints)"  \
  OPT_CONFIG_C_CPP \
  OPT_CONFIG_PLATFORM \
  OPT_CONFIG_BACKEND \
  OPT_CONFIG_LIBRARY \
  OPT_GOTO_CHECK \
  OPT_XML_INTERFACE \
  OPT_JSON_INTERFACE \
  OPT_SOLVER \
  OPT_STRING_REFINEMENT_CBMC \
  OPT_SHOW_GOTO_FUNCTIONS \
  OPT_SHOW_PROPERTIES \
  "(show-symbol-table)(show-parse-tree)" \
  "(drop-unused-functions)" \
  "(havoc-undefined-functions)" \
  "(property):(subproperty):(stop-on-fail)(trace)" \
  "(verbosity):(no-library)" \
  "(nondet-static)" \
  "(version)" \
  OPT_COVER \
  "(symex-coverage-report):" \
  "(mm):" \
  OPT_TIMESTAMP \
  "(arrays-uf-always)(arrays-uf-never)" \
  OPT_FLUSH \
  "(localize-faults)" \
  OPT_GOTO_TRACE \
  OPT_VALIDATE \
  OPT_ANSI_C_LANGUAGE \
  "(claim):(show-claims)(floatbv)(all-claims)(all-properties)" // legacy, and will eventually disappear // NOLINT(whitespace/line_length)
// clang-format on

class cbmc_parse_optionst : public parse_options_baset
{
public:
  virtual int doit() override;
  virtual void help() override;

  cbmc_parse_optionst(int argc, const char **argv);
  cbmc_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

  /// \brief Set the options that have default values
  ///
  /// This function can be called from clients that wish to emulate CBMC's
  /// default behaviour, for example unit tests.
  static void set_default_options(optionst &);

  static bool process_goto_program(goto_modelt &, const optionst &, messaget &);

  static int get_goto_program(
    goto_modelt &,
    const optionst &,
    const cmdlinet &,
    ui_message_handlert &,
    const std::function<void(const goto_modelt &)> &before_processing = {});

protected:
  goto_modelt goto_model;

  void register_languages() override;
  void get_command_line_options(optionst &);
  void preprocessing(const optionst &);
  bool set_properties();
};

#endif // CPROVER_CBMC_CBMC_PARSE_OPTIONS_H
