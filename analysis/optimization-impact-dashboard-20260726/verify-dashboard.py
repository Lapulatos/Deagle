#!/usr/bin/env python3

import json
import re
from pathlib import Path

from playwright.sync_api import sync_playwright


ROOT = Path(__file__).resolve().parent
HTML = ROOT / "deagle-optimization-impact.html"
SCREENSHOT = ROOT / "dashboard-verification.png"
BASE_DATA = json.loads((ROOT / "optimization-impact-data.json").read_text())
HTML_TEXT = HTML.read_text()
embedded_match = re.search(
    r"\bconst DATA = (\{[^\n]+\});\n    const rows = DATA\.rows;",
    HTML_TEXT,
)
assert embedded_match is not None
EMBEDDED_DATA = json.loads(embedded_match.group(1))
assert EMBEDDED_DATA == BASE_DATA
DATA = EMBEDDED_DATA

v284 = next(row for row in DATA["rows"] if row["version"] == 284)
v285 = next(row for row in DATA["rows"] if row["version"] == 285)
assert v284["timing"]["start_iso"] == "2026-07-28T21:35:05.525Z"
assert v284["timing"]["end_iso"] == "2026-07-29T06:34:39.126Z"
assert v285["timing"]["available"] is True
assert v285["timing"]["start_iso"] == "2026-07-29T06:44:08.000Z"
assert v285["timing"]["end_iso"] == "2026-07-29T09:47:33.000Z"
assert v285["timing"]["duration_minutes"] == 183.41666666666666
assert v285["timing"]["start_epoch_s"] > v284["timing"]["end_epoch_s"]
assert "strictly post-v284" in v285["description"].lower()

assert DATA["rows"][0]["metrics"]["memory_sum_b"] == 68299001856
assert next(
    row for row in DATA["rows"] if row["version"] == 193
)["metrics"]["memory_sum_b"] == 34302844928
v194 = next(row for row in DATA["rows"] if row["version"] == 194)
assert v194["status"] == "successful"
assert v194["metrics"]["correct"] == 653
assert v194["metrics"]["memory_sum_b"] == 33770532864
assert "reclassified as successful" in v194["description"]
v195 = next(row for row in DATA["rows"] if row["version"] == 195)
assert v195["status"] == "successful"
assert v195["metrics"]["correct"] == 652
assert v195["metrics"]["memory_sum_b"] == 33926967296
assert "zero wrong results" in v195["description"]
v196 = next(row for row in DATA["rows"] if row["version"] == 196)
assert v196["status"] == "failed"
assert v196["metrics"]["correct"] == 649
assert v196["metrics"]["cpu_s"] == 2744.48038766
assert v196["metrics"]["wall_s"] == 2772.914761819644
assert v196["metrics"]["memory_sum_b"] == 33788190720
assert v196["timing"]["duration_minutes"] == 79.73333333333333
v197 = next(row for row in DATA["rows"] if row["version"] == 197)
assert v197["status"] == "failed"
assert v197["metrics"]["correct"] == 652
assert v197["metrics"]["cpu_s"] == 2697.993791595
assert v197["metrics"]["wall_s"] == 2725.744948232197
assert v197["metrics"]["memory_sum_b"] == 33622917120
assert v197["timing"]["duration_minutes"] == 10.833333333333334
v198 = next(row for row in DATA["rows"] if row["version"] == 198)
assert v198["status"] == "failed"
assert v198["scope"] == "target_or_audit"
assert v198["metrics"]["correct"] is None
assert v198["metrics"]["cpu_s"] is None
assert v198["metrics"]["memory_sum_b"] is None
assert v198["timing"]["duration_minutes"] == 4.716666666666667
v199 = next(row for row in DATA["rows"] if row["version"] == 199)
assert v199["status"] == "failed"
assert v199["scope"] == "exact725"
assert v199["metrics"]["correct"] == 652
assert v199["metrics"]["cpu_s"] == 2699.786823212
assert v199["metrics"]["wall_s"] == 2728.2076069434406
assert v199["metrics"]["memory_sum_b"] == 33674092544
assert v199["timing"]["duration_minutes"] == 14.5
assert "soundness repair candidate" in v199["description"]
v200 = next(row for row in DATA["rows"] if row["version"] == 200)
assert v200["status"] == "failed"
assert v200["scope"] == "exact725"
assert v200["metrics"]["correct"] == 652
assert v200["metrics"]["cpu_s"] == 2609.548366901
assert v200["metrics"]["wall_s"] == 2639.3167088910704
assert v200["metrics"]["memory_sum_b"] == 33739116544
assert v200["timing"]["duration_minutes"] == 25.916666666666668
assert "bounded_buffer timeout" in v200["description"]
v201 = next(row for row in DATA["rows"] if row["version"] == 201)
assert v201["status"] == "failed"
assert v201["scope"] == "target_or_audit"
assert v201["metrics"]["correct"] is None
assert v201["metrics"]["cpu_s"] is None
assert v201["metrics"]["memory_sum_b"] is None
assert v201["timing"]["duration_minutes"] == 3.4
assert "pruned zero RF candidates" in v201["description"]
v202 = next(row for row in DATA["rows"] if row["version"] == 202)
assert v202["status"] == "failed"
assert v202["scope"] == "target_or_audit"
assert v202["metrics"]["correct"] is None
assert v202["metrics"]["cpu_s"] is None
assert v202["metrics"]["memory_sum_b"] is None
assert v202["timing"]["duration_minutes"] == 14.733333333333333
assert "all 80 natural logs pruned zero candidates" in v202["description"]
v203 = next(row for row in DATA["rows"] if row["version"] == 203)
assert v203["status"] == "successful"
assert v203["scope"] == "exact725"
assert v203["metrics"]["correct"] == 653
assert v203["metrics"]["cpu_s"] == 2507.050019702
assert v203["metrics"]["wall_s"] == 2537.199433997
assert v203["metrics"]["memory_sum_b"] == 26844622848
assert v203["timing"]["duration_minutes"] == 43.36666666666667
assert "adds bounded_buffer" in v203["description"]
v204 = next(row for row in DATA["rows"] if row["version"] == 204)
assert v204["status"] == "failed"
assert v204["scope"] == "target_or_audit"
assert v204["metrics"]["correct"] is None
assert v204["metrics"]["cpu_s"] is None
assert v204["metrics"]["memory_sum_b"] is None
assert v204["timing"]["duration_minutes"] == 1.2
assert "zero timeout/OOM tasks" in v204["description"]
v205 = next(row for row in DATA["rows"] if row["version"] == 205)
assert v205["status"] == "audit"
assert v205["scope"] == "target_or_audit"
assert v205["metrics"]["correct"] is None
assert v205["metrics"]["cpu_s"] is None
assert v205["metrics"]["memory_sum_b"] is None
assert v205["timing"]["duration_minutes"] == 7.316666666666666
assert "All 30 tasks across eight families" in v205["description"]
v206 = next(row for row in DATA["rows"] if row["version"] == 206)
assert v206["status"] == "failed"
assert v206["scope"] == "target_or_audit"
assert v206["metrics"]["correct"] is None
assert v206["metrics"]["cpu_s"] is None
assert v206["metrics"]["memory_sum_b"] is None
assert v206["timing"]["duration_minutes"] == 41.45
assert "proved 1/6 natural gate tasks" in v206["description"]
v207 = next(row for row in DATA["rows"] if row["version"] == 207)
assert v207["status"] == "failed"
assert v207["scope"] == "target_or_audit"
assert v207["metrics"]["correct"] is None
assert v207["metrics"]["cpu_s"] is None
assert v207["metrics"]["memory_sum_b"] is None
assert v207["timing"]["duration_minutes"] == 10.85
assert "added two correct natural results" in v207["description"]
v208 = next(row for row in DATA["rows"] if row["version"] == 208)
assert v208["status"] == "failed"
assert v208["scope"] == "target_or_audit"
assert v208["metrics"]["correct"] is None
assert v208["metrics"]["cpu_s"] is None
assert v208["metrics"]["memory_sum_b"] is None
assert v208["timing"]["duration_minutes"] == 4.433333333333334
assert "zero new property-seeded predicates" in v208["description"]
v209 = next(row for row in DATA["rows"] if row["version"] == 209)
assert v209["status"] == "failed"
assert v209["scope"] == "target_or_audit"
assert v209["metrics"]["correct"] is None
assert v209["metrics"]["cpu_s"] is None
assert v209["metrics"]["memory_sum_b"] is None
assert v209["timing"]["duration_minutes"] == 12.1
assert "invalidated" in v209["description"]
v210 = next(row for row in DATA["rows"] if row["version"] == 210)
assert v210["status"] == "failed"
assert v210["scope"] == "target_or_audit"
assert v210["metrics"]["correct"] is None
assert v210["metrics"]["cpu_s"] is None
assert v210["metrics"]["memory_sum_b"] is None
assert v210["timing"]["duration_minutes"] == 11.716666666666667
assert "GOTO-only correctly retained 2/2" in v210["description"]
v211 = next(row for row in DATA["rows"] if row["version"] == 211)
assert v211["status"] == "failed"
assert v211["scope"] == "target_or_audit"
assert v211["metrics"]["correct"] is None
assert v211["metrics"]["cpu_s"] is None
assert v211["metrics"]["memory_sum_b"] is None
assert v211["timing"]["duration_minutes"] == 5.083333333333333
assert "regressed from TRUE to UNKNOWN" in v211["description"]
v212 = next(row for row in DATA["rows"] if row["version"] == 212)
assert v212["status"] == "failed"
assert v212["scope"] == "target_or_audit"
assert v212["metrics"]["correct"] is None
assert v212["metrics"]["cpu_s"] is None
assert v212["metrics"]["memory_sum_b"] is None
assert v212["timing"]["duration_minutes"] == 4.966666666666667
assert "zero assertion symbols" in v212["description"]
v213 = next(row for row in DATA["rows"] if row["version"] == 213)
assert v213["status"] == "failed"
assert v213["scope"] == "target_or_audit"
assert v213["metrics"]["correct"] is None
assert v213["metrics"]["cpu_s"] is None
assert v213["metrics"]["memory_sum_b"] is None
assert v213["timing"]["duration_minutes"] == 4.566666666666666
assert "preserved both known proofs" in v213["description"]
v214 = next(row for row in DATA["rows"] if row["version"] == 214)
assert v214["status"] == "failed"
assert v214["scope"] == "target_or_audit"
assert v214["metrics"]["correct"] is None
assert v214["metrics"]["cpu_s"] is None
assert v214["metrics"]["memory_sum_b"] is None
assert v214["timing"]["duration_minutes"] == 4.783333333333333
assert "Depth one retained 1/2" in v214["description"]
v215 = next(row for row in DATA["rows"] if row["version"] == 215)
assert v215["status"] == "failed"
assert v215["scope"] == "target_or_audit"
assert v215["metrics"]["correct"] is None
assert v215["metrics"]["cpu_s"] is None
assert v215["metrics"]["memory_sum_b"] is None
assert v215["timing"]["duration_minutes"] == 5.066666666666666
assert "added no correct task or second family" in v215["description"]
v216 = next(row for row in DATA["rows"] if row["version"] == 216)
assert v216["status"] == "audit"
assert v216["scope"] == "target_or_audit"
assert v216["metrics"]["correct"] is None
assert v216["metrics"]["cpu_s"] is None
assert v216["metrics"]["memory_sum_b"] is None
assert v216["timing"]["duration_minutes"] == 11.083333333333334
assert "guarded affine transition domain" in v216["description"]
v217 = next(row for row in DATA["rows"] if row["version"] == 217)
assert v217["status"] == "successful"
assert v217["scope"] == "exact725"
assert v217["metrics"]["correct"] == 656
assert v217["metrics"]["cpu_s"] == 2398.9619804769977
assert v217["metrics"]["wall_s"] == 2429.3490511418786
assert v217["metrics"]["memory_sum_b"] == 29535916032
assert v217["timing"]["duration_minutes"] == 91.75
assert "adds three adjudicated-correct exact725 results" in v217["description"]
v218 = next(row for row in DATA["rows"] if row["version"] == 218)
assert v218["status"] == "successful"
assert v218["scope"] == "exact725"
assert v218["metrics"]["correct"] == 656
assert v218["metrics"]["cpu_s"] == 2331.5011063990005
assert v218["metrics"]["wall_s"] == 2362.812985364115
assert v218["metrics"]["memory_sum_b"] == 26734747648
assert v218["timing"]["duration_minutes"] == 27.3
assert "aggregate CPU falls 7.00%" in v218["description"]
v219 = next(row for row in DATA["rows"] if row["version"] == 219)
assert v219["status"] == "failed"
assert v219["scope"] == "target_or_audit"
assert v219["metrics"]["correct"] is None
assert v219["metrics"]["cpu_s"] is None
assert v219["metrics"]["memory_sum_b"] is None
assert v219["timing"]["duration_minutes"] == 1.1166666666666667
assert "rejected by source audit" in v219["description"]
v220 = next(row for row in DATA["rows"] if row["version"] == 220)
assert v220["status"] == "failed"
assert v220["scope"] == "exact725"
assert v220["metrics"]["correct"] == 656
assert v220["metrics"]["cpu_s"] == 2334.55347143
assert v220["metrics"]["memory_sum_b"] == 26732269568
v221 = next(row for row in DATA["rows"] if row["version"] == 221)
assert v221["status"] == "successful"
assert v221["scope"] == "exact725"
assert v221["metrics"]["correct"] == 658
assert v221["metrics"]["cpu_s"] == 2214.72797363
assert v221["metrics"]["wall_s"] == 2246.6477038895246
assert v221["metrics"]["memory_sum_b"] == 26623918080
assert "adds exactly two" in v221["description"]
v222 = next(row for row in DATA["rows"] if row["version"] == 222)
assert v222["status"] == "successful"
assert v222["scope"] == "exact725"
assert v222["metrics"]["correct"] == 658
assert v222["metrics"]["cpu_s"] == 2214.670303445
assert v222["metrics"]["wall_s"] == 2246.3932147194864
assert v222["metrics"]["memory_sum_b"] == 26560638976
assert "accepted server-side baseline" in v222["description"]

v223 = next(row for row in DATA["rows"] if row["version"] == 223)
assert v223["status"] == "failed"
assert v223["scope"] == "target_or_audit"

v224 = next(row for row in DATA["rows"] if row["version"] == 224)
assert v224["status"] == "failed"
assert v224["scope"] == "target_or_audit"

v225 = next(row for row in DATA["rows"] if row["version"] == 225)
assert v225["status"] == "failed"
assert v225["scope"] == "exact725"
assert v225["metrics"]["correct"] == 658
assert v225["metrics"]["cpu_s"] == 2275.044592594
assert v225["metrics"]["wall_s"] == 2304.927760864375
assert v225["metrics"]["memory_sum_b"] == 26571001856

v226 = next(row for row in DATA["rows"] if row["version"] == 226)
assert v226["status"] == "successful"
assert v226["scope"] == "exact725"
assert v226["metrics"]["correct"] == 661
assert v226["metrics"]["cpu_s"] == 2088.109734479
assert v226["metrics"]["wall_s"] == 2118.2589659522055
assert v226["metrics"]["memory_sum_b"] == 26072727552
assert "accepted server-side baseline" in v226["description"]
v227 = next(row for row in DATA["rows"] if row["version"] == 227)
assert v227["status"] == "failed"
assert v227["scope"] == "target_or_audit"
assert v227["metrics"]["correct"] is None
assert "zero SAFE results" in v227["description"]
v228 = next(row for row in DATA["rows"] if row["version"] == 228)
assert v228["status"] == "failed"
assert v228["scope"] == "target_or_audit"
assert v228["metrics"]["correct"] is None
assert "suggested bound of 10001" in v228["description"]
v229 = next(row for row in DATA["rows"] if row["version"] == 229)
assert v229["status"] == "failed"
assert v229["scope"] == "target_or_audit"
assert v229["metrics"]["correct"] is None
assert "reachable-error mutation is falsely SAFE" in v229["description"]
v230 = next(row for row in DATA["rows"] if row["version"] == 230)
assert v230["status"] == "failed"
assert v230["scope"] == "target_or_audit"
assert v230["metrics"]["correct"] is None
assert v230["timing"]["duration_minutes"] == 9.283333333333333
assert "zero complete results" in v230["description"]
v231 = next(row for row in DATA["rows"] if row["version"] == 231)
assert v231["status"] == "failed"
assert v231["scope"] == "target_or_audit"
assert v231["metrics"]["correct"] is None
assert v231["timing"]["duration_minutes"] == 4.033333333333333
assert "indexed value correspondence" in v231["description"]
v232 = next(row for row in DATA["rows"] if row["version"] == 232)
assert v232["status"] == "failed"
assert v232["scope"] == "target_or_audit"
assert v232["metrics"]["correct"] is None
assert v232["timing"]["duration_minutes"] == 2.6666666666666665
assert "largest coherent class contains two inputs" in v232["description"]
v233 = next(row for row in DATA["rows"] if row["version"] == 233)
assert v233["status"] == "failed"
assert v233["scope"] == "exact725"
assert v233["metrics"]["correct"] == 662
assert v233["metrics"]["cpu_s"] == 2017.290621126
assert v233["metrics"]["wall_s"] == 2047.9121288815513
assert v233["metrics"]["memory_sum_b"] == 25765847040
assert abs(v233["timing"]["duration_minutes"] - 25.499516665935516) < 1e-12
assert "39_rand_lock_p0_vs" in v233["description"]

v234 = next(row for row in DATA["rows"] if row["version"] == 234)
assert v234["status"] == "successful"
assert v234["scope"] == "exact725"
assert v234["metrics"]["correct"] == 663
assert v234["metrics"]["cpu_s"] == 1963.809157165
assert v234["metrics"]["wall_s"] == 1994.8034674422815
assert v234["metrics"]["memory_sum_b"] == 26248269824
assert abs(v234["timing"]["duration_minutes"] - 10.543437429269154) < 1e-12
assert "zero losses" in v234["description"]
assert "two ticket" in v234["description"]

v235 = next(row for row in DATA["rows"] if row["version"] == 235)
assert v235["status"] == "failed"
assert abs(v235["timing"]["duration_minutes"] - 0.7333333333333333) < 1e-12

v236 = next(row for row in DATA["rows"] if row["version"] == 236)
assert v236["status"] == "failed"
assert abs(v236["timing"]["duration_minutes"] - 2.5) < 1e-12

v237 = next(row for row in DATA["rows"] if row["version"] == 237)
assert v237["status"] == "successful"
assert v237["scope"] == "exact725"
assert v237["metrics"]["correct"] == 665
assert v237["metrics"]["cpu_s"] == 1848.7006519090003
assert v237["metrics"]["wall_s"] == 1878.6482470136834
assert v237["metrics"]["memory_sum_b"] == 26592956416
assert abs(v237["timing"]["duration_minutes"] - 23.5) < 1e-12
assert "zero losses" in v237["description"]
assert "Twelve mutations" in v237["description"]

v238 = next(row for row in DATA["rows"] if row["version"] == 238)
assert v238["status"] == "successful"
assert v238["scope"] == "exact725"
assert v238["metrics"]["correct"] == 667
assert v238["metrics"]["cpu_s"] == 1728.197979525
assert v238["metrics"]["wall_s"] == 1757.655124468496
assert v238["metrics"]["memory_sum_b"] == 26244182016
assert abs(v238["timing"]["duration_minutes"] - 34.35) < 1e-12
assert "zero losses" in v238["description"]
assert "Twelve mutations" in v238["description"]
v239 = next(row for row in DATA["rows"] if row["version"] == 239)
assert v239["status"] == "successful"
assert v239["scope"] == "exact725"
assert v239["metrics"]["correct"] == 669
assert v239["metrics"]["cpu_s"] == 1717.407047352
assert v239["metrics"]["wall_s"] == 1747.2697022235952
assert v239["metrics"]["memory_sum_b"] == 25972404224
assert abs(v239["timing"]["duration_minutes"] - 33.06666666666667) < 1e-12
assert "zero losses" in v239["description"]
assert "Nineteen semantic mutations" in v239["description"]
v240 = next(row for row in DATA["rows"] if row["version"] == 240)
assert v240["status"] == "successful"
assert v240["scope"] == "exact725"
assert v240["metrics"]["correct"] == 671
assert v240["metrics"]["cpu_s"] == 1709.147737256
assert v240["metrics"]["wall_s"] == 1739.520209371578
assert v240["metrics"]["memory_sum_b"] == 24954265600
assert abs(v240["timing"]["duration_minutes"] - 22.666666666666668) < 1e-12
assert "zero losses" in v240["description"]
assert "Twenty-three semantic mutations" in v240["description"]
v241 = next(row for row in DATA["rows"] if row["version"] == 241)
assert v241["status"] == "failed"
assert v241["metrics"]["correct"] == 671
assert v241["metrics"]["cpu_s"] == v240["metrics"]["cpu_s"]
assert v241["metrics"]["wall_s"] == v240["metrics"]["wall_s"]
assert v241["metrics"]["memory_sum_b"] == v240["metrics"]["memory_sum_b"]
assert "V241 is rejected" in v241["description"]
v242 = next(row for row in DATA["rows"] if row["version"] == 242)
assert v242["status"] == "failed"
assert v242["metrics"]["correct"] == 671
assert "three expected-unsafe tasks" in v242["description"]
v243 = next(row for row in DATA["rows"] if row["version"] == 243)
assert v243["status"] == "successful"
assert v243["scope"] == "exact725"
assert v243["metrics"]["correct"] == 672
assert v243["metrics"]["cpu_s"] == 1655.989678153
assert v243["metrics"]["wall_s"] == 1686.4829210561002
assert v243["metrics"]["memory_sum_b"] == 24991068160
assert "zero losses" in v243["description"]
assert "16/16 semantic mutations" in v243["description"]
v244 = next(row for row in DATA["rows"] if row["version"] == 244)
assert v244["status"] == "failed"
assert v244["metrics"]["correct"] == 672
assert "signed-char width-reduced mutation" in v244["description"]
v245 = next(row for row in DATA["rows"] if row["version"] == 245)
assert v245["status"] == "successful"
assert v245["scope"] == "exact725"
assert v245["metrics"]["correct"] == 673
assert v245["metrics"]["cpu_s"] == 1598.747031391
assert v245["metrics"]["wall_s"] == 1629.126979312161
assert v245["metrics"]["memory_sum_b"] == 25394925568
assert "zero losses" in v245["description"]
assert "16/16 semantic mutations" in v245["description"]
v246 = next(row for row in DATA["rows"] if row["version"] == 246)
assert v246["status"] == "successful"
assert v246["scope"] == "exact725"
assert v246["metrics"]["correct"] == 674
assert v246["metrics"]["cpu_s"] == 1598.872494703
assert v246["metrics"]["wall_s"] == 1629.326790784602
assert v246["metrics"]["memory_sum_b"] == 25456803840
assert "zero losses" in v246["description"]
assert "16/16 counterexample-breaking mutations" in v246["description"]
v247 = next(row for row in DATA["rows"] if row["version"] == 247)
assert v247["status"] == "successful"
assert v247["scope"] == "exact725"
assert v247["metrics"]["correct"] == 675
assert v247["metrics"]["cpu_s"] == 1603.095127337
assert v247["metrics"]["wall_s"] == 1633.377046019421
assert v247["metrics"]["memory_sum_b"] == 25774977024
assert "zero losses" in v247["description"]
assert "16/16 semantic mutations" in v247["description"]
v248 = next(row for row in DATA["rows"] if row["version"] == 248)
assert v248["status"] == "successful"
assert v248["scope"] == "exact725"
assert v248["metrics"]["correct"] == 676
assert v248["metrics"]["cpu_s"] == 1547.515635386
assert v248["metrics"]["wall_s"] == 1577.4903934490867
assert v248["metrics"]["memory_sum_b"] == 25715171328
assert "zero losses" in v248["description"]
assert "17/17 semantic mutations" in v248["description"]
v249 = next(row for row in DATA["rows"] if row["version"] == 249)
assert v249["status"] == "successful"
assert v249["scope"] == "exact725"
assert v249["metrics"]["correct"] == 677
assert v249["metrics"]["cpu_s"] == 1494.787371362
assert v249["metrics"]["wall_s"] == 1524.5379580240697
assert v249["metrics"]["memory_sum_b"] == 25680318464
assert "zero losses" in v249["description"]
assert "17/17 semantic mutations" in v249["description"]
v250 = next(row for row in DATA["rows"] if row["version"] == 250)
assert v250["status"] == "successful"
assert v250["scope"] == "exact725"
assert v250["metrics"]["correct"] == 678
assert v250["metrics"]["cpu_s"] == 1438.993138961
assert v250["metrics"]["wall_s"] == 1469.1238685994176
assert v250["metrics"]["memory_sum_b"] == 25627951104
assert "zero losses" in v250["description"]
assert "18/18 semantic mutations" in v250["description"]
v251 = next(row for row in DATA["rows"] if row["version"] == 251)
assert v251["status"] == "successful"
assert v251["scope"] == "exact725"
assert v251["metrics"]["correct"] == 679
assert v251["metrics"]["cpu_s"] == 1381.278470579
assert v251["metrics"]["wall_s"] == 1414.290667127585
assert v251["metrics"]["memory_sum_b"] == 25679564800
assert "zero losses" in v251["description"]
assert "18/18 semantic mutations" in v251["description"]
v252 = next(row for row in DATA["rows"] if row["version"] == 252)
assert v252["status"] == "successful"
assert v252["scope"] == "exact725"
assert v252["metrics"]["correct"] == 680
assert v252["metrics"]["cpu_s"] == 1323.6970582230006
assert v252["metrics"]["wall_s"] == 1353.9723155956017
assert v252["metrics"]["memory_sum_b"] == 25302093824
assert "zero losses" in v252["description"]
assert "18/18 semantic mutations" in v252["description"]
v253 = next(row for row in DATA["rows"] if row["version"] == 253)
assert v253["status"] == "successful"
assert v253["scope"] == "exact725"
assert v253["metrics"]["correct"] == 681
assert v253["metrics"]["cpu_s"] == 1264.8053403299996
assert v253["metrics"]["wall_s"] == 1294.9803815060295
assert v253["metrics"]["memory_sum_b"] == 25216737280
assert "zero losses" in v253["description"]
assert "18/18 semantic mutations" in v253["description"]
v254 = next(row for row in DATA["rows"] if row["version"] == 254)
assert v254["status"] == "successful"
assert v254["scope"] == "exact725"
assert v254["metrics"]["correct"] == 682
assert v254["metrics"]["cpu_s"] == 1203.4617203379987
assert v254["metrics"]["wall_s"] == 1233.667673881282
assert v254["metrics"]["memory_sum_b"] == 24696680448
assert "zero losses" in v254["description"]
assert "18/18 semantic mutations" in v254["description"]
v255 = next(row for row in DATA["rows"] if row["version"] == 255)
assert v255["status"] == "failed"
assert v255["scope"] == "target_or_audit"
assert v255["metrics"]["correct"] is None
assert v255["metrics"]["cpu_s"] is None
assert v255["metrics"]["wall_s"] is None
assert v255["metrics"]["memory_sum_b"] is None
assert v255["timing"]["duration_minutes"] == 6.183333333333334
assert "signed machine integers" in v255["description"]
assert "duplicate-candidate regression audit" in v255["description"]
native_redo_expected = {
    256: (684, 1204.4573272090006, 24467214336),
    257: (685, 1207.4749497639991, 24502198272),
}
for version, (wrapper_correct, wrapper_cpu, wrapper_memory) in (
    native_redo_expected.items()
):
    row = next(row for row in DATA["rows"] if row["version"] == version)
    assert row["status"] == "successful"
    assert row["scope"] == "exact725"
    assert row["contribution_class"] == "native_consolidated_redo"
    assert row["metrics"]["correct"] == 685
    assert row["metrics"]["cpu_s"] == 1174.583025949
    assert row["metrics"]["wall_s"] == 1200.549746716977
    assert row["metrics"]["memory_sum_b"] == 25778589696
    assert row["wrapper_metrics"]["correct"] == wrapper_correct
    assert row["wrapper_metrics"]["cpu_s"] == wrapper_cpu
    assert row["wrapper_metrics"]["memory_sum_b"] == wrapper_memory
    description = row["description"].lower()
    assert "consolidated" in description
    assert "native" in description

v258 = next(row for row in DATA["rows"] if row["version"] == 258)
assert v258["status"] == "successful"
assert v258["scope"] == "exact725"
assert v258["contribution_class"] == "native_redo"
assert v258["metrics"]["correct"] == 686
assert v258["metrics"]["cpu_s"] == 1227.181420144
assert v258["metrics"]["wall_s"] == 1256.8216319811763
assert v258["metrics"]["memory_sum_b"] == 25570484224
assert v258["wrapper_metrics"]["correct"] == 686
assert v258["wrapper_metrics"]["cpu_s"] == 1208.065720532
assert v258["wrapper_metrics"]["memory_sum_b"] == 24514752512
assert "coverage gain, not a speedup" in v258["description"]

v259 = next(row for row in DATA["rows"] if row["version"] == 259)
assert v259["status"] == "successful"
assert v259["scope"] == "exact725"
assert v259["contribution_class"] == "native_redo"
assert v259["metrics"]["correct"] == 687
assert v259["metrics"]["cpu_s"] == 1175.713834218
assert v259["metrics"]["wall_s"] == 1197.3521209484898
assert v259["metrics"]["memory_sum_b"] == 26466152448
assert v259["wrapper_metrics"]["correct"] == 687
assert v259["wrapper_metrics"]["cpu_s"] == 1215.256050987
assert v259["wrapper_metrics"]["memory_sum_b"] == 24574001152
assert "native v259 redo" in v259["description"].lower()

v260 = next(row for row in DATA["rows"] if row["version"] == 260)
assert v260["status"] == "successful"
assert v260["scope"] == "exact725"
assert v260["contribution_class"] == "native_redo"
assert v260["metrics"]["correct"] == 688
assert v260["metrics"]["cpu_s"] == 1178.834081838
assert v260["metrics"]["wall_s"] == 1201.4165163246216
assert v260["metrics"]["memory_sum_b"] == 26873638912
assert v260["wrapper_metrics"]["correct"] == 688
assert v260["wrapper_metrics"]["cpu_s"] == 1214.183022833
assert v260["wrapper_metrics"]["memory_sum_b"] == 24667418624
assert "native v260 redo" in v260["description"].lower()

v261 = next(row for row in DATA["rows"] if row["version"] == 261)
assert v261["status"] == "successful"
assert v261["scope"] == "exact725"
assert v261["contribution_class"] == "native_redo"
assert v261["metrics"]["correct"] == 689
assert v261["metrics"]["cpu_s"] == 1181.942264104
assert v261["metrics"]["wall_s"] == 1204.2129293229664
assert v261["metrics"]["memory_sum_b"] == 26563518464
assert v261["wrapper_metrics"]["correct"] == 689
assert v261["wrapper_metrics"]["cpu_s"] == 1224.081985708
assert v261["wrapper_metrics"]["memory_sum_b"] == 24465362944
assert "native v261 redo" in v261["description"].lower()

v262 = next(row for row in DATA["rows"] if row["version"] == 262)
assert v262["status"] == "successful"
assert v262["scope"] == "exact725"
assert v262["contribution_class"] == "native_redo"
assert v262["metrics"]["correct"] == 690
assert v262["metrics"]["cpu_s"] == 1189.129119127
assert v262["metrics"]["wall_s"] == 1211.324997216463
assert v262["metrics"]["memory_sum_b"] == 26724327424
assert v262["wrapper_metrics"]["correct"] == 690
assert v262["wrapper_metrics"]["cpu_s"] == 1227.160429512
assert v262["wrapper_metrics"]["memory_sum_b"] == 24557170688
assert "native v262 redo" in v262["description"].lower()

v263 = next(row for row in DATA["rows"] if row["version"] == 263)
assert v263["status"] == "successful"
assert v263["scope"] == "exact725"
assert v263["contribution_class"] == "native_redo"
assert v263["metrics"]["correct"] == 691
assert v263["metrics"]["cpu_s"] == 1250.195763952
assert v263["metrics"]["wall_s"] == 1290.9734508773545
assert v263["metrics"]["memory_sum_b"] == 27473588224
assert v263["wrapper_metrics"]["correct"] == 691
assert v263["wrapper_metrics"]["cpu_s"] == 1164.09645089
assert v263["wrapper_metrics"]["memory_sum_b"] == 24674693120
assert "native v263 redo" in v263["description"].lower()

v264 = next(row for row in DATA["rows"] if row["version"] == 264)
assert v264["status"] == "failed"
assert v264["metrics"]["correct"] is None
assert "task specialization" in v264["description"].lower()

v265 = next(row for row in DATA["rows"] if row["version"] == 265)
assert v265["status"] == "failed"
assert v265["metrics"]["correct"] is None
assert "performance gate" in v265["description"].lower()

v266 = next(row for row in DATA["rows"] if row["version"] == 266)
assert v266["status"] == "successful"
assert v266["scope"] == "exact725"
assert v266["contribution_class"] == "native_redo"
assert v266["metrics"]["correct"] == 692
assert v266["metrics"]["cpu_s"] == 1256.417101767
assert v266["metrics"]["wall_s"] == 1296.6684456527
assert v266["metrics"]["memory_sum_b"] == 27706974208
assert v266["wrapper_metrics"] is None
assert "native mutex-zero fixed-point safety" in v266["description"].lower()

v267 = next(row for row in DATA["rows"] if row["version"] == 267)
assert v267["status"] == "successful"
assert v267["scope"] == "exact725"
assert v267["contribution_class"] == "native_redo"
assert v267["metrics"]["correct"] == 694
assert v267["metrics"]["cpu_s"] == 1136.34285141
assert v267["metrics"]["wall_s"] == 1175.9259267748566
assert v267["metrics"]["memory_sum_b"] == 27560644608
assert v267["wrapper_metrics"] is None
assert "native resolved-worker zero-sum safety" in v267["description"].lower()
assert "run variance" in v267["description"].lower()

v268 = next(row for row in DATA["rows"] if row["version"] == 268)
assert v268["status"] == "successful"
assert v268["scope"] == "exact725"
assert v268["contribution_class"] == "native_redo"
assert v268["metrics"]["correct"] == 695
assert v268["metrics"]["cpu_s"] == 1034.871633912
assert v268["metrics"]["wall_s"] == 1063.7983498902759
assert v268["metrics"]["memory_sum_b"] == 27592212480
assert v268["wrapper_metrics"] is None
assert "native aggregate-member lock-alias safety" in v268["description"].lower()

v269 = next(row for row in DATA["rows"] if row["version"] == 269)
assert v269["status"] == "failed"
assert v269["scope"] == "target_or_audit"
assert v269["contribution_class"] == "verifier_or_audit"
assert v269["metrics"]["correct"] is None
assert v269["wrapper_metrics"] is None
assert "truth gate" in v269["description"].lower()
assert "fully unwound sequential witnesses" in v269["description"].lower()

v270 = next(row for row in DATA["rows"] if row["version"] == 270)
assert v270["status"] == "successful"
assert v270["scope"] == "exact725"
assert v270["contribution_class"] == "native_redo"
assert v270["metrics"]["correct"] == 696
assert v270["metrics"]["cpu_s"] == 1068.617481672
assert v270["metrics"]["wall_s"] == 1109.139516892843
assert v270["metrics"]["memory_sum_b"] == 27364478976
assert v270["wrapper_metrics"] is None
assert "native nested-lifecycle last-writer safety" in v270["description"].lower()
assert "zero losses and zero new wrong" in v270["description"].lower()

v276 = next(row for row in DATA["rows"] if row["version"] == 276)
assert v276["status"] == "failed"
assert v276["scope"] == "target_or_audit"
assert v276["contribution_class"] == "verifier_or_audit"
assert v276["metrics"]["correct"] is None
assert v276["wrapper_metrics"] is None
assert v276["timing"]["available"] is True
assert v276["timing"]["duration_minutes"] == 21.933333333333334
assert "42-step sc schedule" in v276["description"].lower()
assert "no production source" in v276["description"].lower()

v277 = next(row for row in DATA["rows"] if row["version"] == 277)
assert v277["status"] == "failed"
assert v277["scope"] == "target_or_audit"
assert v277["contribution_class"] == "verifier_or_audit"
assert v277["metrics"]["correct"] is None
assert v277["wrapper_metrics"] is None
assert v277["timing"]["available"] is True
assert v277["timing"]["duration_minutes"] == 4.933333333333334
assert "3,868 retained events" in v277["description"]
assert "no production source" in v277["description"].lower()

v278 = next(row for row in DATA["rows"] if row["version"] == 278)
assert v278["status"] == "failed"
assert v278["scope"] == "target_or_audit"
assert v278["contribution_class"] == "verifier_or_audit"
assert v278["metrics"]["correct"] is None
assert v278["wrapper_metrics"] is None
assert v278["timing"]["available"] is True
assert v278["timing"]["duration_minutes"] == 24.4
assert "pthread create/join bodies" in v278["description"].lower()
assert "one new wrong result" in v278["description"].lower()
assert "restored byte-for-byte" in v278["description"].lower()

v279 = next(row for row in DATA["rows"] if row["version"] == 279)
assert v279["status"] == "failed"
assert v279["scope"] == "target_or_audit"
assert v279["contribution_class"] == "verifier_or_audit"
assert v279["metrics"]["correct"] is None
assert v279["wrapper_metrics"] is None
assert v279["timing"]["available"] is True
assert v279["timing"]["duration_minutes"] == 2.966666666666667
assert "first element, whose value is 29" in v279["description"].lower()
assert "one worker and exits 10" in v279["description"].lower()
assert "would therefore introduce a wrong result" in v279["description"].lower()

v280 = next(row for row in DATA["rows"] if row["version"] == 280)
assert v280["status"] == "failed"
assert v280["scope"] == "target_or_audit"
assert v280["contribution_class"] == "verifier_or_audit"
assert v280["metrics"]["correct"] is None
assert v280["wrapper_metrics"] is None
assert v280["timing"]["available"] is True
assert v280["timing"]["duration_minutes"] == 5.75
assert "five invalid asm controls rejected" in v280["description"].lower()
assert "nonempty x86 hardware instructions" in v280["description"].lower()
assert "adds zero coverage" in v280["description"].lower()

v281 = next(row for row in DATA["rows"] if row["version"] == 281)
assert v281["status"] == "successful"
assert v281["scope"] == "exact725"
assert v281["contribution_class"] == "native_redo"
assert v281["metrics"]["correct"] == 698
assert v281["metrics"]["cpu_s"] == 946.604792418
assert v281["metrics"]["wall_s"] == 986.5009775378
assert v281["metrics"]["memory_sum_b"] == 27215429632
assert v281["metrics"]["correct_vs_previous_success"] == 1
assert v281["wrapper_metrics"] is None
assert v281["timing"]["available"] is True
assert v281["timing"]["duration_minutes"] == 92.81666666666666
assert "zero old-correct losses" in v281["description"].lower()
assert "zero new wrong results" in v281["description"].lower()
assert "stale-object contaminated run" in v281["description"].lower()

v282 = next(row for row in DATA["rows"] if row["version"] == 282)
assert v282["status"] == "successful"
assert v282["scope"] == "exact725"
assert v282["metrics"]["correct"] == 699
assert v282["metrics"]["cpu_s"] == 883.906323
assert v282["metrics"]["wall_s"] == 924.530255
assert v282["metrics"]["memory_sum_b"] == 26961915904

v283 = next(row for row in DATA["rows"] if row["version"] == 283)
assert v283["status"] == "successful"
assert v283["scope"] == "exact725"
assert v283["contribution_class"] == "native_redo"
assert v283["metrics"]["correct"] == 699
assert v283["metrics"]["cpu_s"] == 919.289765
assert v283["metrics"]["wall_s"] == 953.451938
assert v283["metrics"]["memory_sum_b"] == 25604014080
assert v283["metrics"]["correct_vs_previous_success"] == 0
assert "zero old-correct losses" in v283["description"].lower()
assert "zero new wrong results" in v283["description"].lower()

v284 = next(row for row in DATA["rows"] if row["version"] == 284)
assert v284["status"] == "successful"
assert v284["scope"] == "exact725"
assert v284["contribution_class"] == "native_redo"
assert v284["metrics"]["correct"] == 700
assert v284["metrics"]["cpu_s"] == 859.041804128
assert v284["metrics"]["wall_s"] == 903.4940643096343
assert v284["metrics"]["memory_sum_b"] == 25426169856
assert v284["metrics"]["correct_vs_previous_success"] == 1
assert "one deagle_exe" in v284["description"].lower()
assert "removes all three python verdict-certificate modules" in v284["description"].lower()
assert "zero old-correct losses" in v284["description"].lower()

v285 = next(row for row in DATA["rows"] if row["version"] == 285)
assert v285["status"] == "successful"
assert v285["scope"] == "exact725"
assert v285["contribution_class"] == "native_redo"
assert v285["metrics"]["correct"] == 701
assert v285["metrics"]["cpu_s"] == 861.356850191
assert v285["metrics"]["wall_s"] == 906.056512353
assert v285["metrics"]["memory_sum_b"] == 25645174784
assert v285["metrics"]["correct_vs_previous_success"] == 1
assert "zero v284-correct losses" in v285["description"].lower()
assert "zero new wrong results" in v285["description"].lower()
assert "earlier 08:55 relational-fold run is discarded" in v285["description"].lower()

v286 = next(row for row in DATA["rows"] if row["version"] == 286)
assert v286["status"] == "failed"
assert v286["scope"] == "exact725"
assert v286["contribution_class"] == "native_redo"
assert v286["metrics"]["correct"] == 701
assert v286["metrics"]["cpu_s"] == 871.2369108290002
assert v286["metrics"]["wall_s"] == 915.1920141403098
assert v286["metrics"]["memory_sum_b"] == 25666789376
assert v286["metrics"]["correct_vs_previous_success"] == 0
assert "ticketlock regressed" in v286["description"].lower()
assert "not committed or pushed" in v286["description"].lower()

v287 = next(row for row in DATA["rows"] if row["version"] == 287)
assert v287["status"] == "successful"
assert v287["scope"] == "exact725"
assert v287["contribution_class"] == "native_redo"
assert v287["metrics"]["correct"] == 702
assert v287["metrics"]["cpu_s"] == 866.534168323
assert v287["metrics"]["wall_s"] == 910.8745472538285
assert v287["metrics"]["memory_sum_b"] == 25625346048
assert v287["metrics"]["correct_vs_previous_success"] == 1
assert "zero v285-correct losses" in v287["description"].lower()
assert "zero new wrong results" in v287["description"].lower()
assert "byte-identical wrapper" in v287["description"].lower()

v288 = next(row for row in DATA["rows"] if row["version"] == 288)
assert v288["status"] == "successful"
assert v288["scope"] == "exact725"
assert v288["contribution_class"] == "native_redo"
assert v288["metrics"]["correct"] == 703
assert v288["metrics"]["cpu_s"] == 865.0478599520001
assert v288["metrics"]["wall_s"] == 908.7999609876424
assert v288["metrics"]["memory_sum_b"] == 25715208192
assert v288["metrics"]["correct_vs_previous_success"] == 1
assert "zero v287-correct losses" in v288["description"].lower()
assert "no other new wrong results" in v288["description"].lower()
assert "byte-identical wrapper" in v288["description"].lower()
assert "task93 remains unknown" in v288["description"].lower()

timing_expected = {
    264: 3.121307483333333,
    265: 6.578901950000001,
    266: 15.261163533333333,
    267: 45.84059726666667,
    268: 41.69801265,
    269: 17.691026016076407,
    270: 68.7,
    276: 21.933333333333334,
    277: 4.933333333333334,
    278: 24.4,
    279: 2.966666666666667,
    280: 5.75,
    281: 92.81666666666666,
    282: 71.76666666666667,
    283: 335.43333333333334,
    284: 539.5600195566813,
    285: 183.41666666666666,
    286: 16.789320416666667,
    287: 25.7,
    288: 19.4,
}
for version, duration in timing_expected.items():
    row = next(row for row in DATA["rows"] if row["version"] == version)
    assert row["timing"]["available"] is True
    assert row["timing"]["duration_minutes"] == duration
    assert row["timing"]["start_iso"]
    assert row["timing"]["end_iso"]


with sync_playwright() as playwright:
    browser = playwright.chromium.launch(headless=True)
    page = browser.new_page(viewport={"width": 1440, "height": 1000})
    console_errors = []
    page.on(
        "console",
        lambda message: console_errors.append(message.text)
        if message.type == "error"
        else None,
    )
    page.goto(HTML.as_uri())
    page.wait_for_load_state("networkidle")

    assert "V1–V288" in page.title()
    assert page.locator("#rangeMax").get_attribute("max") == "288"
    assert page.locator("#rangeMax").input_value() == "288"
    for version, correct in (
        (259, 687), (260, 688), (261, 689), (262, 690), (263, 691),
        (266, 692), (267, 694), (268, 695), (270, 696),
    ):
        assert page.locator(f".point[data-version='{version}']").count() >= 1
        assert str(correct) in page.locator(f"#row-{version}").inner_text()
    for version in (264, 265, 269, 272, 273, 274, 275, 276, 277, 278, 279, 280):
        assert "失败" in page.locator(f"#row-{version}").inner_text()
    assert "成功" in page.locator("#row-283").inner_text()
    assert "699" in page.locator("#row-283").inner_text()
    assert "成功" in page.locator("#row-284").inner_text()
    assert "700" in page.locator("#row-284").inner_text()
    assert "成功" in page.locator("#row-285").inner_text()
    assert "701" in page.locator("#row-285").inner_text()
    assert "676" not in page.locator("#row-285").inner_text()
    assert "失败" in page.locator("#row-286").inner_text()
    assert "701" in page.locator("#row-286").inner_text()
    assert "成功" in page.locator("#row-287").inner_text()
    assert "702" in page.locator("#row-287").inner_text()
    assert "成功" in page.locator("#row-288").inner_text()
    assert "703" in page.locator("#row-288").inner_text()
    assert page.locator(".point[data-version='258']").count() >= 1
    assert "686" in page.locator("#row-258").inner_text()
    for version in (256, 257):
        assert page.locator(f".point[data-version='{version}']").count() >= 1
        assert "685" in page.locator(f"#row-{version}").inner_text()
    assert page.locator(".point[data-version='254']").count() >= 1
    assert page.locator("#chart .point").count() >= 200
    # One header, Baseline, and V1--V288.
    assert page.locator("#ledger .ledger-row").count() == 290
    for version, duration_text in (
        (264, "3.12 min"),
        (265, "6.58 min"),
        (266, "15.26 min"),
        (267, "45.84 min"),
        (268, "41.7 min"),
        (269, "17.69 min"),
        (270, "68.7 min"),
        (276, "21.93 min"),
        (277, "4.93 min"),
        (278, "24.4 min"),
        (279, "2.97 min"),
        (280, "5.75 min"),
        (281, "92.82 min"),
        (282, "71.77 min"),
        (283, "335.43 min"),
        (284, "539.56 min"),
        (285, "183.42 min"),
        (286, "16.79 min"),
        (287, "25.7 min"),
        (288, "19.4 min"),
    ):
        row_text = page.locator(f"#row-{version}").inner_text()
        assert "时间不可确定" not in row_text
        assert duration_text in row_text
    assert "07/29 14:44 → 07/29 17:47" in page.locator("#row-285").inner_text()
    assert "时间不可确定" not in page.locator("#row-220").inner_text()
    assert "40.3 min" in page.locator("#row-220").inner_text()
    assert "时间不可确定" not in page.locator("#row-228").inner_text()
    assert "6.48 min" in page.locator("#row-228").inner_text()
    assert "时间不可确定" not in page.locator("#row-229").inner_text()
    assert "23 min" in page.locator("#row-229").inner_text()
    assert "时间不可确定" not in page.locator("#row-230").inner_text()
    assert "9.28 min" in page.locator("#row-230").inner_text()
    assert "时间不可确定" not in page.locator("#row-231").inner_text()
    assert "4.03 min" in page.locator("#row-231").inner_text()
    assert "时间不可确定" not in page.locator("#row-232").inner_text()
    assert "2.67 min" in page.locator("#row-232").inner_text()
    assert "时间不可确定" not in page.locator("#row-233").inner_text()
    assert "25.5 min" in page.locator("#row-233").inner_text()
    assert "时间不可确定" not in page.locator("#row-234").inner_text()
    assert "10.54 min" in page.locator("#row-234").inner_text()
    assert "时间不可确定" not in page.locator("#row-235").inner_text()
    assert "0.73 min" in page.locator("#row-235").inner_text()
    assert "时间不可确定" not in page.locator("#row-236").inner_text()
    assert "2.5 min" in page.locator("#row-236").inner_text()
    assert "时间不可确定" not in page.locator("#row-237").inner_text()
    assert "23.5 min" in page.locator("#row-237").inner_text()
    assert "时间不可确定" not in page.locator("#row-238").inner_text()
    assert "34.35 min" in page.locator("#row-238").inner_text()
    assert "时间不可确定" not in page.locator("#row-239").inner_text()
    assert "33.07 min" in page.locator("#row-239").inner_text()
    assert "时间不可确定" not in page.locator("#row-240").inner_text()
    assert "22.67 min" in page.locator("#row-240").inner_text()
    assert "时间不可确定" not in page.locator("#row-247").inner_text()
    assert "14.25 min" in page.locator("#row-247").inner_text()
    assert "时间不可确定" not in page.locator("#row-248").inner_text()
    assert "4.93 min" in page.locator("#row-248").inner_text()
    assert "时间不可确定" not in page.locator("#row-249").inner_text()
    assert "4.35 min" in page.locator("#row-249").inner_text()
    assert "时间不可确定" not in page.locator("#row-250").inner_text()
    assert "6.78 min" in page.locator("#row-250").inner_text()
    assert "时间不可确定" not in page.locator("#row-251").inner_text()
    assert "5.27 min" in page.locator("#row-251").inner_text()
    assert "时间不可确定" not in page.locator("#row-252").inner_text()
    assert "16.63 min" in page.locator("#row-252").inner_text()
    assert "时间不可确定" not in page.locator("#row-253").inner_text()
    assert "8.58 min" in page.locator("#row-253").inner_text()
    assert "时间不可确定" not in page.locator("#row-254").inner_text()
    assert "8.73 min" in page.locator("#row-254").inner_text()
    assert "时间不可确定" not in page.locator("#row-255").inner_text()
    assert "6.18 min" in page.locator("#row-255").inner_text()
    assert "时间不可确定" not in page.locator("#row-256").inner_text()
    assert "7.03 min" in page.locator("#row-256").inner_text()
    assert "时间不可确定" not in page.locator("#row-257").inner_text()
    assert "4.43 min" in page.locator("#row-257").inner_text()
    assert "时间不可确定" not in page.locator("#row-258").inner_text()
    assert "4.3 min" in page.locator("#row-258").inner_text()
    assert "时间不可确定" not in page.locator("#row-259").inner_text()
    assert "9.55 min" in page.locator("#row-259").inner_text()
    assert "时间不可确定" not in page.locator("#row-260").inner_text()
    assert "4.8 min" in page.locator("#row-260").inner_text()
    assert "时间不可确定" not in page.locator("#row-261").inner_text()
    assert "4.3 min" in page.locator("#row-261").inner_text()
    assert "时间不可确定" not in page.locator("#row-262").inner_text()
    assert "4.1 min" in page.locator("#row-262").inner_text()
    assert "时间不可确定" not in page.locator("#row-263").inner_text()
    assert "6.55 min" in page.locator("#row-263").inner_text()
    assert "Pristine cloned Deagle" in page.locator("#ledger").inner_text()
    assert "Watched CO-FR Event-Driven Shadow" in page.locator("#ledger").inner_text()
    assert "Counterexample-Only Shallow Prepass" in page.locator("#ledger").inner_text()
    assert "Conditional Lock-Acquisition Transfer" in page.locator("#ledger").inner_text()
    assert "Container-Induced Dynamic Region Provenance" in page.locator("#ledger").inner_text()
    assert "Conditional Event Generation" in page.locator("#ledger").inner_text()
    assert "Dynamic-Allocation Dereference Event Guards" in page.locator("#ledger").inner_text()
    assert "Guard-Conflict Read-From Pruning" in page.locator("#ledger").inner_text()
    assert "Latest Local Write RF Dominance" in page.locator("#ledger").inner_text()
    assert "Property-Relevant Concurrent Event Cone" in page.locator("#ledger").inner_text()
    assert "Synchronization-Relevance Closure Audit" in page.locator("#ledger").inner_text()
    assert "Residual Early-Stage Attribution" in page.locator("#ledger").inner_text()

    page.get_by_role("button", name="CPU总时长").click()
    assert "CPU总时长" in page.locator("#chart").text_content()
    page.get_by_role("button", name="相对基线").click()
    assert "相对最初基线" in page.locator("#chart").text_content()

    page.get_by_role("button", name="总内存开销").click()
    assert "总内存开销" in page.locator("#chart").text_content()
    assert "68.299 GB" in page.locator("#ledger").inner_text()

    page.get_by_role("button", name="研发与验收墙钟跨度").click()
    assert "研发与验收墙钟跨度" in page.locator("#chart").text_content()
    assert page.locator("#chart .point").count() >= 175
    assert page.locator(".point[data-version='254']").count() >= 2

    page.locator(".point[data-version='46']").first.hover()
    assert page.locator("#tooltip.visible").count() == 1
    assert "Counterexample-Only Shallow Prepass" in page.locator("#tooltip").inner_text()
    assert "优化开始" in page.locator("#tooltip").inner_text()
    assert "13.83 min" in page.locator("#tooltip").inner_text()
    assert "总内存" in page.locator("#ledger .ledger-row.header").inner_text()
    assert "研发验收起止 / 墙钟跨度" in page.locator("#ledger .ledger-row.header").inner_text()

    page.locator("#search").fill("Conditional Lock-Acquisition")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V193" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Latest Local Write RF")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V202" in page.locator("#ledger").inner_text()
    assert "all 80 natural logs pruned zero candidates" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Multi-Target Dereference Guard")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V198" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Conditional Event Generation")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V199" in page.locator("#ledger").inner_text()
    assert "soundness repair" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Dynamic-Allocation Dereference")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V200" in page.locator("#ledger").inner_text()
    assert "bounded_buffer timeout" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Guard-Conflict Read-From")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V201" in page.locator("#ledger").inner_text()
    assert "pruned zero RF candidates" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Property-Relevant Concurrent Event Cone")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V203" in page.locator("#ledger").inner_text()
    assert "653" in page.locator("#ledger").inner_text()
    assert "成功" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Synchronization-Relevance Closure Audit")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V204" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "5.68%" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Residual Early-Stage Attribution")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V205" in page.locator("#ledger").inner_text()
    assert "审计" in page.locator("#ledger").inner_text()
    assert "30 tasks across eight families" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Guarded Mutex-Region Fixed Point")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V206" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "1/6 natural gate tasks" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Interference-Closed WP Predicate Synthesis")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V207" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "two correct natural results" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Property-Seeded WP Refinement")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V208" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "zero new property-seeded predicates" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("WP Origin Proof-Core Attribution")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V209" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "invalidated" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Controlled WP Seed-Origin Replication")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V210" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "GOTO-only correctly retained 2/2" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Cyclic-GOTO WP Refinement")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V211" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "regressed from TRUE to UNKNOWN" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Property-Overlap GOTO WP Refinement")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V212" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "zero assertion symbols" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Error-Control GOTO WP Refinement")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V213" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "preserved both known proofs" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Error-Control WP Depth Minimization")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V214" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "Depth one retained 1/2" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Error-Control Depth-2 Combined Natural Gate")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V215" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "added no correct task or second family" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Relational Proof-Gap Audit")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V216" in page.locator("#ledger").inner_text()
    assert "审计" in page.locator("#ledger").inner_text()
    assert "guarded affine transition domain" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Guarded Affine Transition Certificate")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V217" in page.locator("#ledger").inner_text()
    assert "656" in page.locator("#ledger").inner_text()
    assert "成功" in page.locator("#ledger").inner_text()
    assert "34.7%" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Integrated Guarded Affine Dispatch")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V218" in page.locator("#ledger").inner_text()
    assert "656" in page.locator("#ledger").inner_text()
    assert "成功" in page.locator("#ledger").inner_text()
    assert "7.00%" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Affine-Only Fail-Closed Dispatch Audit")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V219" in page.locator("#ledger").inner_text()
    assert "失败" in page.locator("#ledger").inner_text()
    assert "rejected by source audit" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")
    page.locator("#search").fill("Post-Affine Combined Proof Dispatch")
    assert page.locator("#ledger .ledger-row").count() == 2
    assert "V221" in page.locator("#ledger").inner_text()
    assert "658" in page.locator("#ledger").inner_text()
    assert "成功" in page.locator("#ledger").inner_text()
    assert "5.01%" in page.locator("#ledger").inner_text()
    page.locator("#search").fill("")

    page.screenshot(path=str(SCREENSHOT), full_page=True)
    assert not console_errors, console_errors
    chart_points = page.locator("#chart .point").count()
    ledger_rows = page.locator("#ledger .ledger-row").count()
    browser.close()

print(
    json.dumps(
        {
            "html": str(HTML),
            "screenshot": str(SCREENSHOT),
            "chart_points": chart_points,
            "ledger_rows_including_header": ledger_rows,
            "console_errors": 0,
            "interactions_checked": [
                "metric switch",
                "comparison-mode switch",
                "summed-memory metric",
                "optimization-duration metric",
                "hover tooltip",
                "method search",
            ],
        },
        ensure_ascii=False,
        indent=2,
    )
)
