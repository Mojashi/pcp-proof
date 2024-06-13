- pcpproof/*/pcp_instance.thy: PCP instance の定義
- pcpproof/*/invariant.thy: invariantの証明と、PCPに解がない証明

## 検証の実行
```sh
isabelle build -j3 -D pcpproof/1110_1__01_11__1_011 -o parallel_proofs=2 -o ML_system_64 -v PCPProof 
```
