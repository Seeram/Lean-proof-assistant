# Podzväzy

Celkovo sa mi začína rysovať projekt Vašej diplomovky v konkrétnych obrysoch.

Snažil som sa v piatok a v nedeľu pochopiť to,
ako sú v mathlib implementované podmonoidy. Sú tam aj
podgrupy, ale tie majú aj inverziu a pre pochopenie veci
mi stačili monoidy.

Išlo mi najmä o to, aby som vám s dobrým svedomím mohol dať implementovať
podzväzy, či tam nie je nejaký zádrhel. Nejaký som našiel (viď koniec
`odd_submonoid2.lean` ale celkovo to je pre Vás zvládnuteľné, myslím.

## Čo je v tomto adresári

 * `odd_submonoid.lean` -- skúšobný súbor, implementoval som fakt, že nepárne prirodzené čísla sú submonoidom prirodzených čísel vybavených násobením a jednotkou. Definoval som submonoid ako štruktúru a potom som z neho vyrobil
monoid. Išlo mi o to, aby som pochopil veci, o nič iné. 
 * `odd_submonoid2.lean` -- to isté, ale inak: využil som už implementované veci v mathlib, aby som odviedol rovnakú robotu. Je tam funkcia, ktorá vezme submonoid a vráti monoid. Tento je potom možné zaregistrovať ako inštanciu typeclass monoid.
 * `sublattice.lean` -- takto si predstavujem, že budú zavedené podzväzy ako štruktúra. Je to priama analógia s monoidmi. Hral som sa s tým pojmom, napísal som tam všeobecnú funkciu ktorá vyrobí z uzavretého intervalu vo zväze podzväz.
 * `try.lean` -- moje pieskovisko, možno tam nájdete niečo poučné.

## Čo chcem, aby ste spravili

Bolo by dobre, aby ste implementovali aspoň sčasti to, čo je v mathlib už hotové pre podmonoidy/podgrupy
a prerobili to na podzväzy. Pri tom asi pochopíte ešte nejaké ďalšie veci -- napríklad coercions,
sú tam implementované tiež.

Nemusí to byť hotové o dva týždne, ale mali by ste sa pohnúť dopredu. Proste to odpisujte, ale
aspoň s čiastočným porozumením.

## Čo bude ďalej

Ak to zvládnete, bude asi nasledovať implementácia pojmu homomorfizmu.

