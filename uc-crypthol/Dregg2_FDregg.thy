(*  Title:      Dregg2_FDregg.thy
    Author:     dregg2 metatheory — whole-protocol UC scaffold (2026-06-07)

    THE IDEAL FUNCTIONALITY F_dregg AND THE UC REALIZATION SCAFFOLD.

    `Dregg2_FCom.thy` discharged the commitment-layer carriers; `Dregg2_Carriers.thy` discharged the
    signature/MAC and hash carriers.  This theory raises the treatment to the WHOLE PROTOCOL: it
    states the dregg2 capability-ledger as an IDEAL FUNCTIONALITY F_dregg and frames the
    realizes-relation the running dregg2 protocol should satisfy under those carriers.

    F_dregg — A CAPABILITY-LEDGER IDEAL FUNCTIONALITY.  The dregg2 metatheory's kernel
    (`metatheory/Dregg2/...`) is a guarded transition system over a state holding, abstractly:
      * `supply`     — total conserved value (the Pedersen-committed amounts; conservation tier),
      * `caps`       — the authority each party holds (capabilities / attenuation),
      * `nullifiers` — the spent-tag set (anti-double-spend).
    The kernel admits a transition ONLY when it is AUTHORIZED (an admissible effect under the holder's
    capabilities) and it must (a) CONSERVE supply and (b) NOT AMPLIFY authority (a derived capability
    is \<le> the held one).  F_dregg is the IDEALISATION: a trusted ledger that, BY CONSTRUCTION, only
    ever performs authorized + conservation-preserving + non-amplifying transitions.  An environment
    interacting with F_dregg is GUARANTEED these invariants with probability 1 (the ideal world has no
    crypto to break); the real protocol inherits them only up to the carrier advantages.

    WHAT IS PROVED (the perfect / structural fragment, all green, no `sorry`):
      * `fdregg_step` — the ideal transition relation, defined so that it FIRES only on authorized,
        conservation-preserving, non-amplifying effects.
      * `fdregg_conserves` / `fdregg_no_amplify` / `fdregg_authorized` — F_dregg maintains the three
        invariants on EVERY admitted step (the ideal-functionality guarantees, with witnesses).
      * `fdregg_run_conserves` — the invariants are preserved along ANY run (reflexive-transitive
        closure): a non-vacuity-checked safety theorem about the whole ideal protocol.
      * `fdregg_inhabited` — a concrete non-trivial run exists (anti-vacuity: F_dregg is not the empty
        relation; there is a genuine authorized transfer).

    WHAT IS HONESTLY OPEN (the computational fragment).  The UC realization
        dregg2-real-protocol  \<le>_UC  F_dregg     (under the §8 carriers)
    is stated as `Dregg2RealizesFDregg` — a predicate in the @{const Constructive_Cryptography.advantage}
    shape (negligible distinguishing advantage between the ideal+simulator and the real protocol).
    The COMPUTATIONAL reduction (build the simulator; bound the advantage by the carrier advantages of
    Dregg2_Carriers/Dregg2_FCom) is NOT proved here — it is the research-open crown.  We give: the
    precise statement, the simulator-existence shape, and the honest reduction-shaped obligation
    `fdregg_realization_under_carriers` whose hypotheses are EXACTLY the carrier negligibilities.
*)

theory Dregg2_FDregg
  imports
    Dregg2_Carriers
    "CryptHOL.Negligible"
begin

section\<open>The ideal-functionality state and its three invariants\<close>

text\<open>We model the F_dregg ledger state abstractly over a value group (the conserved supply), a
capability with an attenuation order (\<open>\<le>\<close>: a derived cap is below the held one), and a nullifier
universe.  This is the minimal structure the dregg2 kernel's conservation + no-amplify +
anti-double-spend invariants live on.\<close>

record ('v, 'cap, 'null) fstate =
  supply     :: 'v                  \<comment> \<open>total conserved value\<close>
  caps       :: "'cap set"          \<comment> \<open>authority currently held (a downward-closed bundle)\<close>
  nullifiers :: "'null set"         \<comment> \<open>spent tags (anti-double-spend)\<close>

text\<open>An EFFECT to be applied.  It carries the capability it claims to exercise, the cap it would
INSTALL (delegation / derive), the value DELTA it claims, and the nullifier it spends.\<close>
record ('v, 'cap, 'null) feffect =
  use_cap   :: 'cap                 \<comment> \<open>the capability invoked\<close>
  give_cap  :: 'cap                 \<comment> \<open>the capability handed off / derived\<close>
  vdelta    :: 'v                   \<comment> \<open>the value moved (must net to conservation)\<close>
  spend     :: 'null                \<comment> \<open>the nullifier consumed\<close>

context
  fixes capLe :: "'cap \<Rightarrow> 'cap \<Rightarrow> bool"   \<comment> \<open>attenuation order: \<open>capLe a b\<close> = \<open>a\<close> is below \<open>b\<close>\<close>
    and admissible :: "('v, 'cap, 'null) fstate \<Rightarrow> ('v, 'cap, 'null) feffect \<Rightarrow> bool"
        \<comment> \<open>the kernel's authorization predicate (effect admissible in this state)\<close>
begin

subsection\<open>The three ideal guarantees as predicates on a step\<close>

text\<open>AUTHORIZED — the invoked cap is genuinely held, and the effect is admissible.\<close>
definition Authorized :: "('v, 'cap, 'null) fstate \<Rightarrow> ('v, 'cap, 'null) feffect \<Rightarrow> bool" where
  "Authorized s e \<longleftrightarrow> use_cap e \<in> caps s \<and> admissible s e \<and> spend e \<notin> nullifiers s"

text\<open>CONSERVES — supply after = supply before (a transfer nets to zero; @{typ 'v} is additive).\<close>
definition Conserves ::
  "('v::comm_monoid_add, 'cap, 'null) fstate \<Rightarrow> ('v, 'cap, 'null) fstate \<Rightarrow> bool" where
  "Conserves s s' \<longleftrightarrow> supply s' = supply s"

text\<open>NO-AMPLIFY — the installed (derived) cap is below the invoked one in the attenuation order.\<close>
definition NoAmplify :: "('v, 'cap, 'null) feffect \<Rightarrow> bool" where
  "NoAmplify e \<longleftrightarrow> capLe (give_cap e) (use_cap e)"

subsection\<open>The ideal transition relation F_dregg\<close>

text\<open>F_dregg fires from \<open>s\<close> to \<open>s'\<close> under effect \<open>e\<close> EXACTLY when the effect is authorized AND
non-amplifying, and the resulting state is the conservation-preserving update: supply unchanged, the
derived cap installed, the nullifier marked spent.  By CONSTRUCTION the ideal functionality can only
take such steps — this is what makes it ideal.\<close>

definition fdregg_step ::
  "('v::comm_monoid_add, 'cap, 'null) fstate \<Rightarrow> ('v, 'cap, 'null) feffect
     \<Rightarrow> ('v, 'cap, 'null) fstate \<Rightarrow> bool" where
  "fdregg_step s e s' \<longleftrightarrow>
     Authorized s e \<and> NoAmplify e \<and>
     s' = s\<lparr> caps := insert (give_cap e) (caps s),
             nullifiers := insert (spend e) (nullifiers s) \<rparr>"

subsection\<open>The ideal guarantees hold on every admitted step (with witnesses)\<close>

theorem fdregg_authorized:
  assumes "fdregg_step s e s'"
  shows "Authorized s e"
  using assms by (simp add: fdregg_step_def)

theorem fdregg_no_amplify:
  assumes "fdregg_step s e s'"
  shows "NoAmplify e"
  using assms by (simp add: fdregg_step_def)

theorem fdregg_conserves:
  assumes "fdregg_step s e s'"
  shows "Conserves s s'"
  using assms by (simp add: fdregg_step_def Conserves_def)

text\<open>The installed cap is genuinely an attenuation of a HELD cap (no authority is conjured): the
derived cap is below a cap that was in the holder's bundle.\<close>
theorem fdregg_derived_cap_attenuates:
  assumes "fdregg_step s e s'"
  shows "\<exists>h \<in> caps s. capLe (give_cap e) h"
  using assms by (auto simp add: fdregg_step_def NoAmplify_def Authorized_def)

text\<open>The spent nullifier was fresh and is now recorded — no double-spend across the step.\<close>
theorem fdregg_nullifier_fresh_then_spent:
  assumes "fdregg_step s e s'"
  shows "spend e \<notin> nullifiers s \<and> spend e \<in> nullifiers s'"
  using assms by (simp add: fdregg_step_def Authorized_def)

subsection\<open>Whole-run safety (the reflexive-transitive closure)\<close>

text\<open>A run is a sequence of ideal steps.  We close \<open>fdregg_step\<close> (existentially over the effect) and
show supply is conserved along ANY run, and the nullifier set only grows (monotone — no replay can
un-spend).  These are the whole-protocol ideal-world safety guarantees an environment relies on.\<close>

inductive fdregg_run ::
  "('v::comm_monoid_add, 'cap, 'null) fstate \<Rightarrow> ('v, 'cap, 'null) fstate \<Rightarrow> bool" where
  refl: "fdregg_run s s"
| step: "fdregg_step s e s' \<Longrightarrow> fdregg_run s' s'' \<Longrightarrow> fdregg_run s s''"

theorem fdregg_run_conserves:
  assumes "fdregg_run s s'"
  shows "supply s' = supply s"
  using assms
  by (induction rule: fdregg_run.induct)
     (auto dest!: fdregg_conserves simp add: Conserves_def)

theorem fdregg_run_nullifiers_monotone:
  assumes "fdregg_run s s'"
  shows "nullifiers s \<subseteq> nullifiers s'"
  using assms
  by (induction rule: fdregg_run.induct) (auto simp add: fdregg_step_def)

theorem fdregg_run_caps_monotone:
  assumes "fdregg_run s s'"
  shows "caps s \<subseteq> caps s'"
  using assms
  by (induction rule: fdregg_run.induct) (auto simp add: fdregg_step_def)

end  \<comment> \<open>context capLe / admissible\<close>


section\<open>Non-vacuity: F_dregg admits a genuine authorized transfer\<close>

text\<open>Anti-vacuity for the WHOLE scaffold.  We exhibit a concrete instantiation — integer value,
natural-number "capability levels" with the usual \<open>\<le>\<close> as attenuation, an \<open>admissible\<close> that always
accepts a held cap — and a non-trivial run that conserves supply yet installs a derived (lower) cap
and spends a fresh nullifier.  This proves @{const fdregg_step} is NOT the empty relation: there is a
real transition, so the safety theorems above are not vacuous.\<close>

definition demo_admissible ::
  "(int, nat, nat) fstate \<Rightarrow> (int, nat, nat) feffect \<Rightarrow> bool" where
  "demo_admissible s e \<longleftrightarrow> True"  \<comment> \<open>the kernel's real predicate is richer; here: accept (witness only)\<close>

lemma fdregg_inhabited:
  "fdregg_step (\<le>) demo_admissible
     \<lparr> supply = (10::int), caps = {5::nat}, nullifiers = {} \<rparr>
     \<lparr> use_cap = 5, give_cap = 3, vdelta = 0, spend = 99 \<rparr>
     \<lparr> supply = 10, caps = {3, 5}, nullifiers = {99} \<rparr>"
  by (simp add: fdregg_step_def Authorized_def NoAmplify_def demo_admissible_def insert_commute)

text\<open>And a two-step RUN whose supply is conserved end-to-end (the run-safety theorem on a witness).\<close>
lemma fdregg_run_inhabited:
  "fdregg_run (\<le>) demo_admissible
     \<lparr> supply = (10::int), caps = {5::nat}, nullifiers = {} \<rparr>
     \<lparr> supply = 10, caps = {3, 5}, nullifiers = {99} \<rparr>"
  by (rule fdregg_run.step[OF fdregg_inhabited fdregg_run.refl])

lemma fdregg_run_inhabited_conserves:
  "supply \<lparr> supply = (10::int), caps = {3::nat, 5}, nullifiers = {99::nat} \<rparr>
     = supply \<lparr> supply = (10::int), caps = {5::nat}, nullifiers = {} \<rparr>"
  using fdregg_run_conserves[OF fdregg_run_inhabited] .


section\<open>The UC realization scaffold (the honest OPEN crown)\<close>

text\<open>The realizes-relation: the running dregg2 protocol UC-emulates F_dregg.  We phrase it in the
@{const Constructive_Cryptography.advantage} idiom of the AFP UC framework: there exists a simulator
\<open>sim\<close> such that no efficient distinguisher tells the real protocol apart from \<open>sim ∘ F_dregg\<close> with
non-negligible advantage.  We keep the resource/converter types abstract (the dregg2 protocol is not
yet packaged as a CryptHOL resource), so this is the STATEMENT SHAPE, parametrised by the advantage
function — exactly the Canetti-dynamic-UC residue `UCBridge.lean` carries.\<close>

locale dregg2_uc =
  fixes real_protocol :: "security \<Rightarrow> 'res"   \<comment> \<open>the dregg2 running protocol (abstract resource)\<close>
    and ideal_fdregg  :: "security \<Rightarrow> 'res"   \<comment> \<open>F_dregg packaged as a resource\<close>
    and simulate      :: "security \<Rightarrow> 'res \<Rightarrow> 'res"  \<comment> \<open>the simulator wrapping the ideal\<close>
    and uc_advantage  :: "'dist \<Rightarrow> 'res \<Rightarrow> 'res \<Rightarrow> real"  \<comment> \<open>distinguishing advantage\<close>
begin

text\<open>THE REALIZES-RELATION (the target theorem, stated, NOT proved): the dregg2 protocol realizes
F_dregg iff some simulator makes every distinguisher's advantage negligible.\<close>
definition Dregg2RealizesFDregg :: bool where
  "Dregg2RealizesFDregg \<longleftrightarrow>
     (\<forall>\<A>. negligible (\<lambda>\<eta>. uc_advantage \<A> (simulate \<eta> (ideal_fdregg \<eta>)) (real_protocol \<eta>)))"

text\<open>THE HONEST REDUCTION OBLIGATION.  The crown theorem dregg2 wants is: the realization holds GIVEN
the §8 carriers.  We state it with the carrier negligibilities AS HYPOTHESES — a signature/MAC
forgery bound and a hash collision bound and a commitment binding bound (the three families closed in
Dregg2_Carriers/Dregg2_FCom) — and a SIMULATOR-EXISTENCE hypothesis that the per-step distinguishing
advantage is bounded by their sum.  The remaining content (CONSTRUCTING the simulator and PROVING that
per-step bound by a hybrid argument) is the research-open reduction.  This lemma discharges the LAST
mile — negligibility is closed under finite sums — making explicit that the realization follows once
the reduction's advantage bound is supplied.\<close>

theorem fdregg_realization_under_carriers:
  fixes forge_adv coll_adv bind_adv :: "'dist \<Rightarrow> advantage"
  assumes forge: "\<And>\<A>. negligible (forge_adv \<A>)"      \<comment> \<open>§1/§8 unforgeability (Dregg2_Carriers)\<close>
      and coll:  "\<And>\<A>. negligible (coll_adv \<A>)"       \<comment> \<open>§4/§5 collision-resistance (Dregg2_Carriers)\<close>
      and bind:  "\<And>\<A>. negligible (bind_adv \<A>)"       \<comment> \<open>§3 binding (Dregg2_FCom)\<close>
      and reduction:
        "\<And>\<A> \<eta>. \<bar>uc_advantage \<A> (simulate \<eta> (ideal_fdregg \<eta>)) (real_protocol \<eta>)\<bar>
                  \<le> forge_adv \<A> \<eta> + coll_adv \<A> \<eta> + bind_adv \<A> \<eta>"
        \<comment> \<open>THE OPEN PART: the hybrid simulator's per-\<eta> advantage bound. Supplying this is the
            research crown; here it is an explicit hypothesis, NOT proved.\<close>
  shows Dregg2RealizesFDregg
  unfolding Dregg2RealizesFDregg_def
proof (intro allI)
  fix \<A>
  have negsum: "negligible (\<lambda>\<eta>. forge_adv \<A> \<eta> + coll_adv \<A> \<eta> + bind_adv \<A> \<eta>)"
    by (intro negligible_plus forge coll bind)
  show "negligible (\<lambda>\<eta>. uc_advantage \<A> (simulate \<eta> (ideal_fdregg \<eta>)) (real_protocol \<eta>))"
    by (rule negligible_le[OF negsum]) (rule reduction)
qed

end  \<comment> \<open>locale dregg2_uc\<close>

text\<open>NON-VACUITY OF THE UC LOCALE.  A degenerate instance where real = ideal and the simulator is the
identity: the advantage is identically 0, so the realization holds unconditionally.  This witnesses
that @{const dregg2_uc.Dregg2RealizesFDregg} is satisfiable — the locale is not contradictory and the
relation is not vacuously empty.  (The REAL instance — the dregg2 protocol as a CryptHOL resource with
a non-trivial simulator and the hybrid reduction — is the open work.)\<close>

interpretation trivial_uc:
  dregg2_uc "\<lambda>_. ()" "\<lambda>_. ()" "\<lambda>_ r. r" "\<lambda>_ _ _. (0::real)" .

lemma trivial_uc_realizes: "trivial_uc.Dregg2RealizesFDregg"
  by (simp add: trivial_uc.Dregg2RealizesFDregg_def)


section\<open>Scaffold summary (machine-side trust seam, whole protocol)\<close>

text\<open>What this theory establishes about the WHOLE protocol:

  PROVED (perfect / structural fragment — the ideal world):
    \<^item> @{const fdregg_step} — F_dregg fires only on authorized + non-amplifying effects, with the
      conservation-preserving update;
    \<^item> @{thm fdregg_authorized} @{thm fdregg_conserves} @{thm fdregg_no_amplify}
      @{thm fdregg_derived_cap_attenuates} @{thm fdregg_nullifier_fresh_then_spent}
      — the per-step ideal guarantees;
    \<^item> @{thm fdregg_run_conserves} @{thm fdregg_run_nullifiers_monotone}
      @{thm fdregg_run_caps_monotone} — whole-run safety;
    \<^item> @{thm fdregg_inhabited} @{thm fdregg_run_inhabited_conserves} — non-vacuity (a genuine run).

  STATED, OPEN (computational fragment — the realization crown):
    \<^item> @{const dregg2_uc.Dregg2RealizesFDregg} — the dregg2 protocol UC-realizes F_dregg;
    \<^item> @{thm dregg2_uc.fdregg_realization_under_carriers} — it FOLLOWS from the §8 carriers ONCE the
      hybrid simulator's per-\<eta> advantage bound (the `reduction` hypothesis) is proved.  That bound —
      constructing the simulator + the hybrid argument over Dregg2_Carriers/Dregg2_FCom advantages —
      is the genuinely research-open part, honestly carried as a hypothesis, never asserted as a
      theorem.\<close>

end
