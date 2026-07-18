# BRIEF — Reprise « Relève de nuit du 18 juillet »

> **Premier message d'une session de reprise.** Colle ce fichier (ou son contenu)
> comme tout premier message de la nouvelle session.
>
> - **Modèle attendu :** Fable 5
> - **Effort :** xhigh
> - **Dépôt :** `SolGi4nni/dregg`
> - **Branche de travail :** `claude/sleep-disconnect-management-x5lit8`
>   (repars de là, ou crée une branche dédiée depuis `main` si la relève avait sa propre ligne)

---

## 0. Autorisations (toutes)

Tu es **pleinement autorisé·e** à mener ce travail de bout en bout, en autonomie,
**sans redemander la permission** à chaque étape :

- lire et explorer tout le dépôt ;
- créer, modifier et supprimer des fichiers du dépôt ;
- exécuter les commandes nécessaires (build, tests, lint, scripts, `git`) ;
- **commit** avec des messages clairs et **push** sur la branche de travail
  ci‑dessus (`git push -u origin <branche>`, avec retries en cas d'erreur réseau).

Garde quand même le réflexe de **confirmer avant une action difficilement
réversible ou tournée vers l'extérieur** (ex. ouvrir une pull request, publier,
supprimer du travail non poussé). Ne crée **pas** de pull request sans demande
explicite.

---

## 1. Pourquoi ce brief existe

La session originale « **Relève de nuit du 18 juillet** » tournait en **Claude Code
dans le terminal d'un Mac**, pilotée à distance depuis le téléphone. Le Mac s'est
**mis en veille / a perdu le Wi‑Fi** en pleine nuit → le contrôle à distance a
affiché *« Contrôle à distance déconnecté — la session dans le terminal a cessé de
répondre »*, et le travail s'est **interrompu**.

Constats vérifiés côté dépôt :

- la session **n'a poussé aucune branche** dédiée (seules `main` et
  `claude/sleep-disconnect-management-x5lit8` existent à distance) → son code
  éventuel est resté **local sur le Mac**, non récupérable tant que le Mac est
  hors ligne ;
- le seul contexte durable est le **transcript partagé** de la session
  (« Session partagée, visible par toute personne disposant du lien »).

**But de cette reprise :** repartir en **session cloud** (indépendante du Mac,
donc insensible à la veille et au Wi‑Fi) et **continuer la relève là où elle s'est
arrêtée**.

---

## 2. Objectif de la relève de nuit — À COMPLÉTER

> ⚠️ **Cette section doit être remplie depuis le transcript partagé** (elle n'a pas
> pu être récupérée automatiquement : le lien de session est protégé par la
> connexion claude.ai). Récupère‑la de l'une de ces façons :
>
> - ouvre la session partagée → **« Gérer »** → copie le **lien public** et
>   colle‑le, **ou**
> - copie‑colle ici les passages clés du transcript, **ou**
> - décris l'objectif en deux phrases.

- **Tâche / objectif principal :** _[à remplir]_
- **Sous‑partie de `dregg` concernée :** _[à remplir — crate / dossier / fichiers]_
- **Contraintes / attendus :** _[à remplir]_

---

## 3. Dernier point connu / état à la reprise — À COMPLÉTER

- **Ce qui était déjà fait :** _[à remplir]_
- **La dernière action en cours au moment de la coupure :** _[à remplir]_
- **Todo / plan restant :** _[à remplir]_

---

## 4. Plan de reprise

1. **Reconstituer le contexte** à partir des sections 2 et 3 (transcript partagé
   ou consignes ci‑dessus). Si un doute subsiste sur l'objectif, poser **une**
   question ciblée, puis avancer.
2. **Faire un bref point de situation** en début de session : « voilà où la relève
   en était, voilà ce que je reprends ».
3. **Reprendre le travail** à la première étape non terminée.
4. **Commit + push réguliers** sur la branche de travail, pour que l'avancement
   soit durable et pilotable du téléphone à tout moment.
5. **Tenir une todo à jour** dans la session, pour qu'une éventuelle nouvelle
   coupure soit triviale à reprendre.

---

## 5. Garde‑fous (pour ne plus jamais perdre la relève)

- **Ne dépends plus du Mac.** Tout le travail vit dans cette session cloud + le
  dépôt distant. Rien d'essentiel ne doit rester uniquement sur la machine locale.
- **Pousse tôt et souvent.** Un commit non poussé peut être perdu ; un commit
  poussé, jamais.
- **Machine locale, pour plus tard :** quand l'accès au Mac est retrouvé, le dépôt
  contient `scripts/keep-mac-awake.sh` (empêche la veille + garde le réseau) —
  `./scripts/keep-mac-awake.sh install` pour que ça ne se reproduise pas.

---

*Ce fichier est un point de reprise. Une fois la relève terminée, il peut être
supprimé ou archivé.*
