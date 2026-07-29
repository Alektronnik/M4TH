# PrimeGapsSophie.web.lean — Compatibilidad Lean v4.33.0-rc1

## Cambios respecto a PrimeGapsSophie.live.lean

| API v4.31.0 (.live) | API v4.33.0-rc1 (.web) |
|---------------------|-------------------------|
| `Nat.infinite_setOf_prime` | `Nat.infinite_setOfPred_prime` |

## Verificacion

```
grep -c 'Nat\.infinite_setOfPred_prime' PrimeGapsSophie.web.lean   # debe dar 3
grep -c 'Nat\.infinite_setOf_prime[^P]' PrimeGapsSophie.web.lean   # debe dar 0
```
