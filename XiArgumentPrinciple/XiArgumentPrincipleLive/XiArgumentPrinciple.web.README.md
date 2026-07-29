# XiArgumentPrinciple.web.lean — Compatibilidad Lean v4.33.0-rc1

## Cambios respecto a XiArgumentPrinciple.live.lean

| API v4.31.0 (.live) | API v4.33.0-rc1 (.web) |
|---------------------|-------------------------|
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |

## Verificacion

```
grep -c 'Set\.mem_ofPred_eq' XiArgumentPrinciple.web.lean   # debe dar 3
grep -c 'Set\.mem_setOf_eq' XiArgumentPrinciple.web.lean    # debe dar 0
```
