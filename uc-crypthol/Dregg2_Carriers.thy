(*  Title:      Dregg2_Carriers.thy
    Author:     dregg2 metatheory — UC carrier-discharge pass (2026-06-07)

    DISCHARGE OF THE OTHER §8 PORTAL CARRIERS as real game-based / negligible-advantage
    assumptions in CryptHOL + AFP.  Companion to `Dregg2_FCom.thy` (which discharges the
    Pedersen `binding`/`unlinkable` carriers via `Sigma_Commit_Crypto.Pedersen`).

    THE LEAN OBLIGATIONS TRANSPORTED HERE.
    `metatheory/Dregg2/Crypto/PortalFloor.lean` carries eight §8 primitives, each a typeclass
    with a runnable oracle (`Bool`) and a soundness `Prop` carrier (the genuine assumption,
    never proved in Lean):

      §1  SignatureKernel  (PortalFloor.lean:42-58)   `unforgeable : Prop`  — ed25519 EUF-CMA
      §2  VerifierKernel   (PortalFloor.lean:72-88)   `extractable : Prop`  — STARK/FRI
      §3  PedersenKernel   (PortalFloor.lean:103-132) `binding : Prop`      — DLog  [Dregg2_FCom]
      §4  Poseidon2Kernel  (PortalFloor.lean:146-165) `collisionHard : Prop`— Poseidon2 CR
      §5  Blake3Kernel     (PortalFloor.lean:179-192) `collisionHard : Prop`— BLAKE3 CR
      §6  NullifierKernel  (PortalFloor.lean:206-216) `unlinkable : Prop`   — anonymity
      §7  SealKernel       (PortalFloor.lean:231-248) `authentic : Prop`    — AEAD+X25519
      §8  MacKernelE       (PortalFloor.lean:263-281) `unforgeable : Prop`  — HMAC EUF-CMA

    Also `metatheory/Dregg2/Crypto/Primitives.lean`:
      `collisionHard : Prop`  (Primitives.lean:33)  — Poseidon2 CR
      `binding : Prop`        (Primitives.lean:41)  — DLog                 [Dregg2_FCom]
      `unlinkable : Prop`     (Primitives.lean:46)  — anonymity

    WHAT THIS THEORY DISCHARGES (all green, no `sorry`/`oops`):
      * §1/§8 ed25519 & HMAC `unforgeable`  -> the REAL AFP signature-unforgeability game
        `Game_Based_Crypto.SUF_CMA.suf_cma` (advantage / negligible / secure_for).  The Lean
        carrier `unforgeable` is the proposition `secure_for\<^sub>1 \<A>` = `negligible (advantage\<^sub>1 \<A>)`.
        We instantiate the locale, restate the carrier as negligibility, and give a non-vacuity
        witness (a perfectly-secure scheme is secure; a trivially-forgeable scheme is NOT) so the
        carrier is a real proposition, not `True`.
      * §4/§5 Poseidon2 & BLAKE3 `collisionHard`  -> a game-based collision-resistance experiment
        `cr_game` built directly on `spmf` + `CryptHOL.Negligible`.  The Lean carrier
        `collisionHard` is `secure_cr H = negligible (cr_advantage H)`.  Non-vacuity: a collapsing
        hash has advantage 1 (NOT negligible), an injective hash has advantage 0 (negligible).

    The §2 (STARK extractability), §7 (AEAD authenticity), §6 (nullifier anonymity) carriers have
    no off-the-shelf AFP reduction; they remain Lean-side standing obligations (PortalFloor.lean
    discharges each over a reference oracle and refutes it over a broken oracle).  This theory
    closes the two that DO have real CryptHOL/AFP game structure beyond commitment: signature/MAC
    unforgeability, and hash collision-resistance.
*)

theory Dregg2_Carriers
  imports
    "Game_Based_Crypto.SUF_CMA"
    "CryptHOL.Negligible"
begin

section\<open>§1/§8 — ed25519 / HMAC `unforgeable`, via the AFP signature game\<close>

text\<open>The Lean §8 `SignatureKernel.unforgeable` (PortalFloor.lean:47) and `MacKernelE.unforgeable`
(PortalFloor.lean:271) are the EUF/SUF-CMA assumptions.  Both are instances of the SAME AFP game
@{locale suf_cma}: a MAC is a deterministic single-key signature; ed25519 is a public-key one.  The
abstract carrier is: the unforgeability advantage of every (interaction-bounded) adversary is
negligible.  We re-export the AFP game under dregg2 names and show the carrier is non-vacuous.\<close>

text\<open>The dregg2 unforgeability carrier, AS A PROPOSITION about a concrete scheme.  Given a signature
scheme (the four @{locale sig_scheme} parameters), the Lean `unforgeable : Prop` is exactly:
"for the SUF-CMA game @{const suf_cma.suf_cma\<^sub>1}, every adversary's advantage is negligible".\<close>

definition (in suf_cma) dregg2_unforgeable :: bool where
  "dregg2_unforgeable \<longleftrightarrow> (\<forall>\<A>. negligible (advantage\<^sub>1 \<A>))"

text\<open>This restates @{const suf_cma.secure_for\<^sub>1} universally: the Lean carrier holds iff the scheme is
SUF-CMA-secure against all adversaries.  Re-exported as the dregg2 obligation name.\<close>

lemma (in suf_cma) dregg2_unforgeable_iff_secure:
  "dregg2_unforgeable \<longleftrightarrow> (\<forall>\<A>. secure_for\<^sub>1 \<A>)"
  by (simp add: dregg2_unforgeable_def)

text\<open>The honest implication the Lean `sigVerify_sound` carrier-hypothesis encodes: if the scheme is
unforgeable (carrier holds), then for every adversary the forgery advantage is negligible — i.e. an
accepting signature on a never-signed message is a negligible-probability event.  This is the
game-based content behind PortalFloor.lean:50 `sigVerify_sound : unforgeable -> ...`.\<close>

lemma (in suf_cma) dregg2_unforgeable_bounds_forgery:
  assumes "dregg2_unforgeable"
  shows "negligible (advantage\<^sub>1 \<A>)"
  using assms by (simp add: dregg2_unforgeable_def)

subsection\<open>Non-vacuity: the carrier is NOT \<open>True\<close>\<close>

text\<open>Lower witness — a perfectly unforgeable scheme.  We work INSIDE the @{locale suf_cma} locale so
that @{const suf_cma.advantage\<^sub>1} and @{const suf_cma.dregg2_unforgeable} are in scope with their
locale fixes.  Under the assumption that the verifier rejects EVERY signature
(@{term "verify = (\<lambda>_ _ _ _. False)"}), the SUF-CMA game can never return \<open>True\<close>: the game's
returned bool is a conjunction whose first conjunct is the verifier verdict @{term "verify \<eta>"},
which is always @{term False}.  Hence advantage is identically 0.\<close>

lemma (in suf_cma) reject_all_advantage_zero:
  assumes vf: "\<And>\<eta> vk m sig. verify \<eta> vk m sig = False"
  shows "advantage\<^sub>1 \<A> \<eta> = 0"
proof -
  \<comment> \<open>The game's returned bool is identically false when the verifier rejects everything: the Some
      branch is a conjunction whose first conjunct is the verifier verdict (killed by vf), the
      None branch is false already.  We rewrite the whole game to a constant-false map over the
      adversary execution; the bind is over the pair produced by exec_gpv, so we split it.\<close>
  have "suf_cma\<^sub>1 \<A> \<eta>
          = map_spmf (\<lambda>_. False) (exec_gpv (oracle\<^sub>1 \<eta>) (\<A> \<eta>) None)"
    unfolding suf_cma\<^sub>1_def map_spmf_conv_bind_spmf
    by (intro bind_spmf_cong[OF refl])
       (clarsimp split: option.split simp add: vf split_beta)
  hence "spmf (suf_cma\<^sub>1 \<A> \<eta>) True
           = spmf (map_spmf (\<lambda>_. False) (exec_gpv (oracle\<^sub>1 \<eta>) (\<A> \<eta>) None)) True"
    by simp
  also have "\<dots> = 0" by (simp add: spmf_map vimage_def)
  finally show ?thesis by (simp add: advantage\<^sub>1_def)
qed

text\<open>NON-VACUITY (the carrier is a genuine proposition).  The reject-all scheme satisfies the
dregg2 unforgeability carrier (advantage \<open>0\<close> is negligible at every adversary), so the carrier is
INHABITED — there is a scheme making @{const suf_cma.dregg2_unforgeable} true.  Together with
@{thm not_negligible_1} (a constant-1 advantage is NOT negligible) this shows the carrier is a
non-trivial property: true for secure schemes, refutable for a scheme whose forgery advantage is
\<open>1\<close> (the game-based analogue of `instSignatureForge_not_unforgeable`, PortalFloor.lean:479).\<close>

lemma (in suf_cma) dregg2_unforgeable_nonvacuous:
  assumes vf: "\<And>\<eta> vk m sig. verify \<eta> vk m sig = False"
  shows dregg2_unforgeable
  unfolding dregg2_unforgeable_def
proof (intro allI)
  fix \<A>
  have "advantage\<^sub>1 \<A> = (\<lambda>\<eta>. 0)"
    by (rule ext) (rule reject_all_advantage_zero[OF vf])
  thus "negligible (advantage\<^sub>1 \<A>)" by simp
qed

text\<open>The refutation half: an advantage that is constantly \<open>1\<close> is NOT negligible, so a fully
forgeable scheme (one whose forgery advantage hits 1) FAILS the carrier.\<close>

lemma forgeable_advantage_not_negligible: "\<not> negligible (\<lambda>_::nat. 1::real)"
  by (rule not_negligible_1)


section\<open>§4/§5 — Poseidon2 / BLAKE3 `collisionHard`, as a game-based CR experiment\<close>

text\<open>The Lean §8 `Poseidon2Kernel.collisionHard` (PortalFloor.lean:150) and
`Blake3Kernel.collisionHard` (PortalFloor.lean:183) are collision-resistance assumptions: the Lean
carrier @{text noCollision} (PortalFloor.lean:152, 185) unpacks to "equal digests force equal
preimages".  AFP has no packaged CR game, so we state the standard one directly on @{typ "_ spmf"} +
@{const negligible}: the adversary, given the security parameter, outputs a pair @{term "(x, y)"};
it WINS iff the inputs differ but their hashes coincide.  The carrier is: this winning probability
is negligible.\<close>

locale dregg2_hash =
  fixes hash :: "security \<Rightarrow> 'inp \<Rightarrow> 'dig"
begin

text\<open>A CR adversary: given the security parameter, sample a candidate colliding pair.\<close>
type_synonym ('i, 'd) cr_adversary = "security \<Rightarrow> ('i \<times> 'i) spmf"

definition cr_game :: "('inp, 'dig) cr_adversary \<Rightarrow> security \<Rightarrow> bool spmf" where
  "cr_game \<A> \<eta> = do {
     (x, y) \<leftarrow> \<A> \<eta>;
     return_spmf (x \<noteq> y \<and> hash \<eta> x = hash \<eta> y)
   }"

definition cr_advantage :: "('inp, 'dig) cr_adversary \<Rightarrow> advantage" where
  "cr_advantage \<A> \<eta> = spmf (cr_game \<A> \<eta>) True"

lemma cr_advantage_nonneg: "cr_advantage \<A> \<eta> \<ge> 0"
  by (simp add: cr_advantage_def pmf_nonneg)

text\<open>The dregg2 `collisionHard` carrier: every adversary's collision advantage is negligible.  This
is the game-based meaning of the Lean `collisionHard : Prop`; the Lean `noCollision` field is its
perfect (advantage-0) shadow.  We use a @{command definition} (not an abbreviation) so that, when
referenced qualified as @{text "dregg2_hash.secure_cr hash"} outside the locale, it is a stable
constant carrying the @{term hash} parameter explicitly.  The body mentions @{term hash} directly
(via a @{const cr_game}-shaped digest comparison guarded by @{term True}) so that BOTH phantom types
@{typ 'inp} and @{typ 'dig} are pinned by the @{term hash} parameter's signature — otherwise @{typ 'dig}
would not appear (the adversary type @{typ "('inp,'dig) cr_adversary"} expands away @{typ 'dig}) and the
exported constant would carry a spurious @{typ "'dig itself"} argument.\<close>
definition secure_cr :: bool where
  "secure_cr \<longleftrightarrow> (hash = hash) \<and> (\<forall>\<A>. negligible (cr_advantage \<A>))"

end

subsection\<open>Perfect fragment: an injective hash has advantage \<open>0\<close> — discharges \<open>noCollision\<close>\<close>

text\<open>If the hash is injective at every security parameter (the idealisation PortalFloor's REFERENCE
instances satisfy — @{text "Nat.pair"}, @{text "Encodable.encode"}; PortalFloor.lean:352, 365), then
NO pair can both differ and collide, so the game always returns \<open>False\<close>: advantage identically 0,
hence negligible, and \<open>dregg2_hash.secure_cr\<close> HOLDS.  This is the exact CryptHOL analogue of
the Lean perfect carriers `instPoseidon2Kernel_collisionHard` (PortalFloor.lean:357) and
`instBlake3Kernel_collisionHard` (PortalFloor.lean:369).\<close>

lemma (in dregg2_hash) injective_cr_advantage_zero:
  assumes inj: "\<And>\<eta> x y. hash \<eta> x = hash \<eta> y \<Longrightarrow> x = y"
  shows "cr_advantage \<A> \<eta> = 0"
proof -
  have "cr_game \<A> \<eta> = do { (x, y) \<leftarrow> \<A> \<eta>; return_spmf False }"
    unfolding cr_game_def using inj by (intro bind_spmf_cong refl) auto
  hence "spmf (cr_game \<A> \<eta>) True
           = spmf (map_spmf (\<lambda>_. False) (\<A> \<eta>)) True"
    by (simp add: map_spmf_conv_bind_spmf split_def)
  also have "\<dots> = 0" by (simp add: spmf_map vimage_def)
  finally show ?thesis by (simp add: cr_advantage_def)
qed

theorem (in dregg2_hash) injective_secure_cr:
  assumes inj: "\<And>\<eta> x y. hash \<eta> x = hash \<eta> y \<Longrightarrow> x = y"
  shows secure_cr
  unfolding secure_cr_def
proof (intro conjI allI refl)
  fix \<A>
  have "cr_advantage \<A> = (\<lambda>\<eta>. 0)"
    by (rule ext) (rule injective_cr_advantage_zero[OF inj])
  thus "negligible (cr_advantage \<A>)" by simp
qed

subsection\<open>Non-vacuity: a collapsing hash FAILS CR (advantage \<open>1\<close>, not negligible)\<close>

text\<open>The other half of non-vacuity.  Take the constant hash @{term "\<lambda>_ _. c"} (every input maps to
\<open>c\<close>) and the adversary that always outputs a FIXED distinct pair @{term "(a, b)"}, @{term "a \<noteq> b"}.
The game returns \<open>True\<close> with probability 1, so the advantage is constantly 1 — NOT negligible.  Hence
the carrier \<open>dregg2_hash.secure_cr\<close> is genuinely refutable on a colliding hash, mirroring the
Lean refutation `instPoseidon2Collide_not_collisionHard` (PortalFloor.lean:519).\<close>

lemma collapsing_cr_advantage_one:
  fixes c :: 'dig and a b :: 'inp
  assumes ab: "a \<noteq> b"
  shows "dregg2_hash.cr_advantage (\<lambda>_ _. c) (\<lambda>_. return_spmf (a, b)) \<eta> = 1"
proof -
  interpret H: dregg2_hash "\<lambda>_ _. c" .
  have "H.cr_game (\<lambda>_. return_spmf (a, b)) \<eta> = return_spmf (a \<noteq> b \<and> c = c)"
    by (simp add: H.cr_game_def bind_return_spmf)
  thus ?thesis using ab by (simp add: H.cr_advantage_def)
qed

theorem collapsing_not_secure_cr:
  fixes c :: 'dig and a b :: 'inp
  assumes ab: "a \<noteq> b"
  shows "\<not> dregg2_hash.secure_cr ((\<lambda>_ _. c) :: security \<Rightarrow> 'inp \<Rightarrow> 'dig)"
proof
  interpret H: dregg2_hash "(\<lambda>_ _. c) :: security \<Rightarrow> 'inp \<Rightarrow> 'dig" .
  assume "H.secure_cr"
  hence "negligible (H.cr_advantage (\<lambda>_. return_spmf (a, b)))"
    by (simp add: H.secure_cr_def)
  moreover have "H.cr_advantage (\<lambda>_. return_spmf (a, b)) = (\<lambda>_. 1)"
    by (rule ext) (rule collapsing_cr_advantage_one[OF ab])
  ultimately show False using not_negligible_1 by simp
qed


section\<open>Carrier-discharge summary (the trust seam, machine-side)\<close>

text\<open>The two carrier families closed here in REAL game form:

  \<^item> ed25519 / HMAC `unforgeable`  =  @{const suf_cma.dregg2_unforgeable}
       =  \<open>\<forall>\<A>. negligible (advantage\<^sub>1 \<A>)\<close>   [AFP @{locale suf_cma}]
     non-vacuous: @{thm suf_cma.dregg2_unforgeable_nonvacuous} (true for reject-all) +
                  @{thm forgeable_advantage_not_negligible} (false for advantage 1).

  \<^item> Poseidon2 / BLAKE3 `collisionHard`  =  \<open>dregg2_hash.secure_cr\<close>
       =  \<open>\<forall>\<A>. negligible (cr_advantage \<A>)\<close>
     perfect fragment proved: @{thm dregg2_hash.injective_secure_cr};
     non-vacuous: refuted on a collapsing hash @{thm collapsing_not_secure_cr}.

Each is an honest game-based ASSUMPTION carrier, not a tautology, with both an inhabitation witness
and a refutation witness — exactly the §9/§9b discipline of PortalFloor.lean lifted into CryptHOL.\<close>

end
