"""Light-weight parsing of Lean 4 pretty-printed signatures (as in explore-data.json).

Not a Lean parser: it splits on bracket depth and recognises the handful of top-level shapes
that NLAlib statements use (relations, set-builder tails, integrals, quantifiers). Every check
built on it reports its own false-positive rate in the audit.
"""
import re

OPEN = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
CLOSE = {v: k for k, v in OPEN.items()}


def norm_ws(s):
    return re.sub(r'\s+', ' ', s).strip()


def _protect(s):
    """Mark set-builder separators `{x | …}` / `{x : T | …}` as ⫽ so `|` means abs elsewhere."""
    return re.sub(r'\{(\s*[^{}|⦃⦄]*?)\s\|\s', r'{\1 ⫽ ', s)


def depth_scan(s):
    """Yield (index, char, depth) with depth counting brackets, ‖…‖ and |…| pairs."""
    stack = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        d = len(stack)
        if c in OPEN:
            yield i, c, d
            stack.append(OPEN[c])
        elif stack and c == stack[-1] and c in CLOSE:
            stack.pop()
            yield i, c, len(stack)
        elif c in '‖|':
            if stack and stack[-1] == c:
                stack.pop()
                yield i, c, len(stack)
            else:
                # opening iff preceded by start, space, open bracket or operator
                prev = s[:i].rstrip()[-1:] if s[:i].strip() else ''
                if prev == '' or prev in '([{⦃⟨,=≤<≥>+-*/•^∑∫¬↑√⬝∧∨→↔∈⊆⫽' or s[i - 1:i] == ' ':
                    yield i, c, d
                    stack.append(c)
                else:
                    yield i, c, d
        else:
            yield i, c, d
        i += 1


BINDER_MEM = re.compile(r'([∑∏⨆⨅∃∀⋃⋂] ?\(?[^,∈]{1,40}?\)?) ∈ ')


def mask_binders(s):
    return BINDER_MEM.sub(lambda m: m.group(1) + ' ∈ᵇ ', s)


def split_top(s, seps):
    """Split s at depth-0 occurrences of any separator string (longest first)."""
    seps = sorted(seps, key=len, reverse=True)
    parts, ops, last = [], [], 0
    skip_to = -1
    for i, c, d in depth_scan(s):
        if i < skip_to or d:
            continue
        for sep in seps:
            if s.startswith(sep, i):
                parts.append(s[last:i])
                ops.append(sep)
                last = i + len(sep)
                skip_to = last
                break
    parts.append(s[last:])
    return parts, ops


def strip_parens(s):
    s = s.strip()
    while s and s[0] in '(' and s[-1] == ')':
        # only strip if the outer pair matches
        depth = 0
        ok = True
        for i, c, d in depth_scan(s):
            if c == ')' and d == 0 and i != len(s) - 1:
                ok = False
                break
        if not ok:
            break
        s = s[1:-1].strip()
    return s


def split_signature(sig):
    """(binders, conclusion) of a pretty-printed signature `Name.{u} binders : concl`."""
    s = _protect(norm_ws(sig))
    # skip the name and universe list
    m = re.match(r'\S+?(\.\{[^}]*\})?\s', s)
    i = m.end() if m else 0
    binders = []
    n = len(s)
    while i < n:
        while i < n and s[i] == ' ':
            i += 1
        if i >= n:
            break
        c = s[i]
        if c in '({[⦃':
            close = OPEN[c]
            depth = 0
            j = i
            while j < n:
                if s[j] in OPEN:
                    depth += 1
                elif s[j] in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            binders.append((c, s[i + 1:j]))
            i = j + 1
        elif c == ':':
            return binders, s[i + 1:].strip()
        else:
            # unexpected token (e.g. a def with no binders); give up on binders
            k = s.find(' : ', i)
            return binders, s[k + 3:].strip() if k >= 0 else ''
    return binders, ''


QUANT_RX = re.compile(r'^(∀ᵐ|∃!|∃|∀)\s')


def _blocks_arrow(prefix):
    """True when a top-level ↔/∧/∨/∀/∃ before the first → means the arrow is inside a body."""
    p2, o2 = split_top(prefix, [' ↔ ', ' ∧ ', ' ∨ '])
    if len(p2) > 1:
        return True
    for i, ch, d in depth_scan(prefix):
        if d == 0 and ch in '∀∃':
            return True
    return False


def peel(concl):
    """Strip outer ∀ / ∀ᵐ / ∃ / → layers. Returns (core, layers) with layers a list of tags."""
    layers = []
    c = strip_parens(concl)
    for _ in range(12):
        m = QUANT_RX.match(c)
        if m:
            parts, ops = split_top(c, [','])
            if len(parts) < 2:
                break
            layers.append({'∀ᵐ': 'ae', '∃': 'exists', '∃!': 'existsUnique', '∀': 'forall'}[m.group(1)])
            c = strip_parens(','.join(parts[1:]))
            continue
        parts, ops = split_top(c, [' → '])
        if len(parts) > 1 and not _blocks_arrow(parts[0]):
            layers.append('imp')
            c = strip_parens(parts[-1])
            continue
        break
    return c, layers


RELS = [' ↔ ', ' ≤ ', ' < ', ' ≥ ', ' > ', ' ≠ ', ' = ', ' ∈ ', ' ∉ ', ' ⊆ ', ' =ᵐ[', ' ≤ᵐ[']
REL_TOK = {'↔': 'iff', '≤': 'le', '<': 'lt', '≥': 'ge', '>': 'gt', '≠': 'ne', '=': 'eq', '∈': 'mem',
           '∉': 'notMem', '⊆': 'subset', '=ᵐ[': 'ae_eq', '≤ᵐ[': 'ae_le'}


def top_relation(core):
    core = mask_binders(core)
    """(lhs, reltoken, rhs) for the lowest-precedence top-level relation, else None.
    ∧/∨ at top level give ('and'|'or')."""
    parts, ops = split_top(core, [' ↔ '])
    if len(parts) > 1:
        return (parts[0].strip(), 'iff', ' ↔ '.join(parts[1:]).strip())
    for conn, tok in ((' ∨ ', 'or'), (' ∧ ', 'and')):
        parts, ops = split_top(core, [conn])
        if len(parts) > 1:
            return (parts[0].strip(), tok, conn.join(parts[1:]).strip())
    parts, ops = split_top(core, RELS[1:])
    if len(parts) > 1:
        op = ops[0].strip()
        return (parts[0].strip(), REL_TOK[op], parts[1].strip() if len(parts) == 2 else
                ops[0].join(parts[1:]).strip())
    return None


IDENT = re.compile(r"[A-Za-z_𝕜α-ωΑ-Ωℓ][\w'₀-₉ᵢⱼₖ!?𝕜]*(\.[A-Za-z_][\w'₀-₉!?]*)*")
GREEK_OR_VAR = re.compile(r"^([A-Za-zα-ωΑ-Ωℓ𝕜][₀-₉'ᵢⱼₖ]*|[a-z][a-z]?[₀-₉']*|xs|ys|hA|θ|τ)$")

BIN_OPS = [(' + ', 'add'), (' - ', 'sub'), (' * ', 'mul'), (' / ', 'div'), (' • ', 'smul'),
           (' ⬝ᵥ ', 'dotProduct'), (' *ᵥ ', 'mulVec'), (' ᵥ* ', 'vecMul'), (' ⊗ₖ ', 'kronecker'),
           (' ∘ ', 'comp'), (' ^ ', 'pow'), (' ⊔ ', 'sup'), (' ⊓ ', 'inf'), (' ∩ ', 'inter'),
           (' ∪ ', 'union')]
PREC = [[' + ', ' - '], [' * ', ' / ', ' • ', ' ⬝ᵥ ', ' *ᵥ ', ' ᵥ* ', ' ⊗ₖ ', ' ∩ ', ' ∪ '], [' ∘ '],
        [' ^ ']]
OPNAME = dict(BIN_OPS)


def last_comp(ident):
    return ident.split('.')[-1]


def lc_first(s):
    return s[:1].lower() + s[1:] if s else s


def head_candidates(e, depth=0):
    """Set of name tokens with which a Mathlib-style name may begin when describing e.
    'VAR' marks a bound variable (any following token allowed)."""
    e = strip_parens(e.strip())
    out = set()
    if not e or depth > 8:
        return {'VAR'}
    for level in PREC:
        parts, ops = split_top(e, level)
        if len(parts) > 1:
            op = OPNAME[ops[0]]
            if op == 'pow':
                expo = parts[1].strip()
                out |= {'sq'} if expo == '2' else {'pow', 'rpow', 'zpow'}
                out |= {'pow'}
            else:
                out.add(op)
            sub = head_candidates(parts[0], depth + 1)
            out |= sub
            if 'VAR' in sub:
                out.add('VAR')
            if op == 'mul' and parts[0].strip() in ('2', '↑2'):
                out.add('two_mul')
            return out
    c = e[0]
    if e.startswith('Var['):
        return {'variance'}
    if e.startswith('cov['):
        return {'covariance'}
    if re.match(r"^[μν]\[", e):
        return {'condExp', 'integral'}
    if re.match(r"^\(Measure\.\w+ .*\)\.real \{", e):
        return {'measureReal'}
    if c == '(':
        depth = 0
        for i, ch in enumerate(e):
            depth += ch == '('
            depth -= ch == ')'
            if depth == 0:
                break
        m2 = re.match(r"^((?:\.[A-Za-z]\w*)+)", e[i + 1:])
        if m2:
            inner = head_candidates(e[1:i], depth + 1) - {'VAR', 'VAR_COE'}
            return {lc_first(x) for x in m2.group(1).split('.') if x} | inner
    if e.startswith('μ.real') or re.match(r"^[μνP][₀-₉']*\.real\b", e) or re.match(r'^\(?\w+\)?\.real ', e):
        return {'measureReal'}
    if re.match(r"^[μνκ][₀-₉']* [{(⫽]", e) or re.match(r'^[μν] \{', e):
        return {'measure'}
    if e.startswith('∫⁻'):
        return {'lintegral'}
    if e.startswith('∫'):
        return {'integral', 'setIntegral'}
    if e.startswith('∑'):
        return {'sum'}
    if e.startswith('∏'):
        return {'prod'}
    if e.startswith('⨆'):
        return {'iSup', 'ciSup'}
    if e.startswith('⨅'):
        return {'iInf', 'ciInf'}
    if e.startswith('‖'):
        inner = e[1:].split('‖')[0]
        r = {'norm', 'nnnorm', 'enorm'}
        if 'toLp' in inner:
            r |= {'norm_toLp'}
        return r
    if e.startswith('|'):
        return {'abs'}
    if e.startswith('√'):
        return {'sqrt'}
    if e.startswith('¬'):
        return {'not'}
    if e.startswith('↑') or e.startswith('⇑'):
        return {'coe', 'cast', 'natCast', 'ofReal', 'VAR_COE'} | head_candidates(e[1:], depth + 1)
    if e.startswith('-'):
        return {'neg'} | head_candidates(e[1:], depth + 1)
    if e.startswith('{'):
        return {'setOf', 'VAR'}
    if e.startswith('fun') or e.startswith('λ'):
        return {'fun', 'VAR'}
    if e.startswith('if '):
        return {'ite'}
    if e.startswith('⟪'):
        return {'inner'}
    if e.startswith('!!') or e.startswith('!['):
        return {'VAR'}
    m = re.match(r'^(\d+)', e)
    if m:
        num = {'0': 'zero', '1': 'one', '2': 'two', '3': 'three', '4': 'four'}.get(m.group(1), 'ofNat')
        return {num, 'ofNat'}
    if e[0] == '⊤':
        return {'top'}
    if e[0] == '⊥':
        return {'bot'}
    if e[0] == '∅':
        return {'empty'}
    # postfix ops: ᴴ ᵀ ⁻¹ ! at the end of the first atom
    m = IDENT.match(e)
    if not m:
        return {'VAR'}
    ident = m.group(0)
    end = m.end()
    while ident and ident[-1] in 'ᴴᵀ':
        ident = ident[:-1]
        end -= 1
    rest = e[end:]
    # (expr).field form handled by strip_parens failing; detect `(…).f`
    comps = ident.split('.')
    head = comps[-1]
    # dotted call on a variable: `A.trace`, `hA.foo`, `(Y ω).trace`
    if len(comps) > 1 and GREEK_OR_VAR.match(comps[0]):
        head = comps[-1]
    elif len(comps) > 1 and comps[0] in ('Matrix', 'Real', 'RCLike', 'NormedSpace', 'Polynomial',
                                          'Finset', 'Fintype', 'Function', 'Complex', 'CFC',
                                          'LinearMap', 'Submodule', 'MeasureTheory',
                                          'ProbabilityTheory', 'Metric', 'NNReal', 'ENNReal',
                                          'Set', 'Nat', 'Int', 'Module', 'WithLp', 'EuclideanSpace',
                                          'NLAlib', 'Lagrange', 'Matrix.IsHermitian'):
        head = comps[-1]
    tok = lc_first(head)
    # suffix postfix operator directly after atom
    post = set()
    if rest.startswith('ᴴ'):
        post.add('conjTranspose')
    if rest.startswith('ᵀ'):
        post.add('transpose')
    if rest.startswith('⁻¹'):
        post.add('inv')
    if GREEK_OR_VAR.match(ident) and not rest.startswith(' '):
        return {'VAR'} | post
    if GREEK_OR_VAR.match(ident):
        # a variable applied to arguments (a function variable `f x`, `X ω`)
        return {'VAR'} | post
    if tok == 'kroneckerMap':
        tok = 'kronecker'
    if len(comps) > 2 and GREEK_OR_VAR.match(comps[0]):
        post |= {lc_first(x) for x in comps[1:]}
    if tok in ('rexp', 'exp'):
        tok = 'exp'
    r = {tok} | post
    if tok == 'exp':
        r |= {'rexp', 'exp'}
    if c == '(' and post:
        r.add('VAR')
    return r


def idents(s):
    """All identifier components occurring in s (for token-presence checks)."""
    out = set()
    for m in IDENT.finditer(s):
        for comp in m.group(0).split('.'):
            out.add(comp)
            out.add(lc_first(comp))
    return out
