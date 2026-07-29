# MertensPNT.web.lean — Compatibilidad Lean v4.33.0-rc1

## Cambios respecto a MertensPNT.live.lean

| API v4.31.0 (.live) | API v4.33.0-rc1 (.web) |
|---------------------|-------------------------|
| `Nat.infinite_setOf_prime` | `Nat.infinite_setOfPred_prime` |

## Fixes adicionales

- `summable_mertensCorrectionIndexed`: `dsimp` reemplazado por `rfl` explicito para `natPrimesEquiv k`. En v4.33.0-rc1 `dsimp` no reduce proyecciones de `Equiv`.
- `mertensPrimeCorrectionSum_eq_tsum_indexed`: idem.

## Verificacion

```
grep -c 'Nat\.infinite_setOfPred_prime' MertensPNT.web.lean   # debe dar 7
grep -c 'Nat\.infinite_setOf_prime[^P]' MertensPNT.web.lean   # debe dar 0
```
