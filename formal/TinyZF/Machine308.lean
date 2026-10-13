import TinyZF.Machine

set_option maxRecDepth 8192

/-! Literal import of candidates/ics-best.tm. Regenerate with formal/tools/generate.py. -/
namespace TinyZF.Machine308

/-- Original labels, in the numeric state order. -/
def labels : Vector String 308 := ⟨#[
  "0.boot.A",
  "0.boot.B",
  "0.boot.C",
  "0.boot.D",
  "0.boot.E",
  "1.decnz",
  "1.decnz.b",
  "1.decnz.c",
  "1.decnz.d",
  "1.decnz.e",
  "1.decnz.g",
  "1.decnz.h",
  "1.decnz.i",
  "1.inc",
  "1.inc.b",
  "1.inc.c",
  "1.inc.d",
  "1.sel",
  "1.sel.b",
  "1.sel.c",
  "1.sel.d",
  "1.sel.e",
  "1.sel.f",
  "2.ret1",
  "2.ret1.1",
  "2.ret1.2",
  "2.ret2",
  "2.ret2.1",
  "2.ret2.2",
  "3.axiomcode.decnz",
  "3.axiomcode.inc",
  "3.nextproof.decnz",
  "3.nextproof.inc",
  "3.param1.decnz",
  "3.param1.inc",
  "3.param2.decnz",
  "3.param2.inc",
  "3.param3.decnz",
  "3.param3.inc",
  "3.prooflist.decnz",
  "3.prooflist.inc",
  "3.scratch1.decnz",
  "3.scratch1.inc",
  "3.scratch2.decnz",
  "3.scratch2.inc",
  "3.topwff.decnz",
  "3.topwff.inc",
  "3.wffstack.decnz",
  "3.wffstack.inc",
  "4.dispatch.1",
  "4.dispatch.2",
  "4.dispatch.3",
  "4.dispatch.4",
  "4.dispatch.5",
  "4.dispatch.6",
  "4.dispatch.7",
  "5.root",
  "6.break.0",
  "6.break.1",
  "6.break.2",
  "6.continue.0",
  "6.continue.1",
  "6.continue.2",
  "6.continue.3",
  "6.continue.4",
  "main().0",
  "main().0.0",
  "main().0.0.0",
  "main().0.1",
  "main().0.1.0",
  "main().0.1.0.0",
  "main().0.1.0.1",
  "main().0.1.1",
  "main().0.1.2",
  "main().1",
  "main().10",
  "main().11",
  "main().12",
  "main().13",
  "main().14",
  "main().15",
  "main().16",
  "main().17",
  "main().18",
  "main().19",
  "main().2",
  "main().2.0",
  "main().20",
  "main().21",
  "main().22",
  "main().23",
  "main().24",
  "main().25",
  "main().26",
  "main().27",
  "main().28",
  "main().28.0",
  "main().29",
  "main().3",
  "main().30",
  "main().30.0",
  "main().30.0.0",
  "main().30.1",
  "main().31",
  "main().31.0",
  "main().32",
  "main().33",
  "main().34",
  "main().35",
  "main().36",
  "main().37",
  "main().38",
  "main().39",
  "main().4",
  "main().40",
  "main().41",
  "main().42",
  "main().43",
  "main().44",
  "main().45",
  "main().46",
  "main().47",
  "main().48",
  "main().49",
  "main().5",
  "main().50",
  "main().51",
  "main().51.0",
  "main().51.0.0",
  "main().51.1",
  "main().51.1.0",
  "main().52",
  "main().52.0",
  "main().52.0.0",
  "main().52.1",
  "main().52.2",
  "main().53",
  "main().54",
  "main().55",
  "main().55.0",
  "main().56",
  "main().57",
  "main().58",
  "main().59",
  "main().6",
  "main().60",
  "main().61",
  "main().62",
  "main().63",
  "main().64",
  "main().65",
  "main().66",
  "main().67",
  "main().68",
  "main().69",
  "main().7",
  "main().70",
  "main().70.0",
  "main().71",
  "main().72",
  "main().73",
  "main().74",
  "main().74.0",
  "main().75",
  "main().76",
  "main().77",
  "main().78",
  "main().79",
  "main().8",
  "main().80",
  "main().81",
  "main().81.0",
  "main().82",
  "main().83",
  "main().84",
  "main().84.0",
  "main().84.1",
  "main().84.1.0",
  "main().9",
  "main().9.0",
  "main().9.0.0",
  "main().9.1",
  "main().9.1.0",
  "main().9.1.1",
  "main().n_001.0",
  "main().n_009.0",
  "main().n_010.0",
  "main().n_011.0",
  "main().n_012.0",
  "main().n_013.0",
  "main().n_014.0",
  "main().n_018.0",
  "main().n_018.0.0",
  "main().n_018.1",
  "main().n_018.2",
  "main().n_021.0",
  "main().n_021.1",
  "main().n_024.0",
  "main().n_024.1",
  "main().n_025.0",
  "main().n_025.0.0",
  "main().n_028.0",
  "main().n_028.1",
  "main().n_029.0",
  "main().n_029.0.0",
  "main().n_035.0",
  "main().n_037.0",
  "main().n_038.0",
  "main().n_042.0",
  "main().n_042.0.0",
  "main().n_042.1",
  "main().n_042.2",
  "main().n_042.3",
  "main().n_044.0",
  "main().n_044.1",
  "main().n_046.0",
  "main().n_046.0.0",
  "main().n_046.0.1",
  "main().n_046.1",
  "main().n_049.0",
  "main().n_050.0",
  "main().n_051.0",
  "main().n_052.0",
  "main().n_053.0",
  "main().n_054.0",
  "main().n_055.0",
  "main().n_056.0",
  "main().n_057.0",
  "main().n_058.0",
  "main().n_060.0",
  "main().n_060.1",
  "main().n_061.0",
  "main().n_062.0",
  "main().n_063.0",
  "main().n_066.0",
  "main().n_066.1",
  "main().n_066.1.0",
  "main().n_067.0",
  "main().n_068.0",
  "main().n_069.0",
  "main().n_070.0",
  "main().n_071.0",
  "main().n_072.0",
  "main().n_073.0",
  "main().n_074.0",
  "main().n_075.0",
  "main().n_076.0",
  "main().n_077.0",
  "main().n_078.0",
  "main().n_079.0",
  "main().n_080.0",
  "main().n_081.0",
  "main().n_082.0",
  "main().n_083.0",
  "main().n_085.0",
  "main().n_085.1",
  "main().n_086.0",
  "main().n_087.0",
  "main().n_089.0",
  "main().n_089.1",
  "main().n_090.0",
  "main().n_092.0",
  "main().n_092.1",
  "main().n_094.0",
  "main().n_094.1",
  "main().n_095.0",
  "main().n_097.0",
  "main().n_098.0",
  "main().n_098.0.0",
  "main().n_099.0",
  "main().n_100.0",
  "main().n_101.0",
  "main().n_109.0",
  "main().n_109.0.0",
  "main().n_109.0.1",
  "main().n_109.0.1.0",
  "main().n_109.0.1.1",
  "main().n_109.0.1.1.0",
  "main().n_109.0.2",
  "main().n_109.0.3",
  "main().n_111.0",
  "main().n_111.1",
  "main().n_122.0",
  "main().n_122.0.0",
  "main().n_122.0.1",
  "main().n_122.0.2",
  "main().n_122.0.2.0",
  "main().n_122.0.3",
  "main().n_122.0.3.0",
  "main().n_122.1",
  "main().n_122.2",
  "main().n_125.0",
  "main().n_126.0",
  "main().n_128.0",
  "main().n_129.0",
  "main().n_130.0",
  "main().n_131.0",
  "main().n_140.0",
  "main().n_143.0",
  "main().n_143.1",
  "main().n_144.0",
  "main().n_145.0",
  "main().n_146.0",
  "main().n_148.0",
  "main().n_148.1",
  "main().n_149.0",
  "main().n_151.0",
  "main().n_153.0",
], by decide⟩

/-- Two transitions per working state, in read-bit order 0,1.
An absent transition and an explicit halt remain distinct. -/
def table : Vector (Option (Transition 308)) 616 := ⟨#[
  some ⟨true, true, some 1⟩, -- 0.boot.A / 0
  some ⟨false, false, some 2⟩, -- 0.boot.A / 1
  some ⟨false, true, some 2⟩, -- 0.boot.B / 0
  some ⟨false, true, some 1⟩, -- 0.boot.B / 1
  some ⟨true, false, some 3⟩, -- 0.boot.C / 0
  some ⟨false, true, some 4⟩, -- 0.boot.C / 1
  some ⟨false, false, some 4⟩, -- 0.boot.D / 0
  some ⟨false, false, some 64⟩, -- 0.boot.D / 1
  some ⟨true, false, some 0⟩, -- 0.boot.E / 0
  some ⟨false, false, some 1⟩, -- 0.boot.E / 1
  some ⟨true, true, some 6⟩, -- 1.decnz / 0
  some ⟨true, false, some 10⟩, -- 1.decnz / 1
  some ⟨false, true, some 6⟩, -- 1.decnz.b / 0
  some ⟨false, true, some 7⟩, -- 1.decnz.b / 1
  some ⟨true, true, some 8⟩, -- 1.decnz.c / 0
  some ⟨true, true, some 7⟩, -- 1.decnz.c / 1
  some ⟨false, true, some 9⟩, -- 1.decnz.d / 0
  some ⟨false, true, some 7⟩, -- 1.decnz.d / 1
  some ⟨false, false, some 5⟩, -- 1.decnz.e / 0
  some ⟨true, true, some 9⟩, -- 1.decnz.e / 1
  some ⟨false, false, some 26⟩, -- 1.decnz.g / 0
  some ⟨true, true, some 11⟩, -- 1.decnz.g / 1
  some ⟨true, true, some 12⟩, -- 1.decnz.h / 0
  some ⟨false, true, some 11⟩, -- 1.decnz.h / 1
  some ⟨false, false, some 17⟩, -- 1.decnz.i / 0
  some ⟨true, true, some 9⟩, -- 1.decnz.i / 1
  some ⟨true, true, some 14⟩, -- 1.inc / 0
  none, -- 1.inc / 1
  some ⟨false, true, some 14⟩, -- 1.inc.b / 0
  some ⟨true, true, some 15⟩, -- 1.inc.b / 1
  some ⟨false, true, some 16⟩, -- 1.inc.c / 0
  some ⟨true, true, some 15⟩, -- 1.inc.c / 1
  some ⟨true, false, some 23⟩, -- 1.inc.d / 0
  some ⟨true, true, some 15⟩, -- 1.inc.d / 1
  some ⟨true, true, some 18⟩, -- 1.sel / 0
  some ⟨false, false, some 23⟩, -- 1.sel / 1
  some ⟨false, true, some 18⟩, -- 1.sel.b / 0
  some ⟨true, true, some 19⟩, -- 1.sel.b / 1
  some ⟨false, true, some 20⟩, -- 1.sel.c / 0
  some ⟨true, true, some 19⟩, -- 1.sel.c / 1
  some ⟨false, false, some 21⟩, -- 1.sel.d / 0
  some ⟨true, true, some 19⟩, -- 1.sel.d / 1
  some ⟨true, false, some 22⟩, -- 1.sel.e / 0
  some ⟨false, false, some 23⟩, -- 1.sel.e / 1
  some ⟨false, true, some 21⟩, -- 1.sel.f / 0
  some ⟨true, false, some 22⟩, -- 1.sel.f / 1
  some ⟨false, false, some 24⟩, -- 2.ret1 / 0
  some ⟨true, false, some 23⟩, -- 2.ret1 / 1
  some ⟨false, false, some 25⟩, -- 2.ret1.1 / 0
  some ⟨true, false, some 23⟩, -- 2.ret1.1 / 1
  some ⟨false, false, some 25⟩, -- 2.ret1.2 / 0
  some ⟨false, false, some 57⟩, -- 2.ret1.2 / 1
  some ⟨false, false, some 27⟩, -- 2.ret2 / 0
  some ⟨true, false, some 26⟩, -- 2.ret2 / 1
  some ⟨false, false, some 28⟩, -- 2.ret2.1 / 0
  some ⟨true, false, some 26⟩, -- 2.ret2.1 / 1
  some ⟨false, false, some 28⟩, -- 2.ret2.2 / 0
  some ⟨false, false, some 58⟩, -- 2.ret2.2 / 1
  some ⟨false, true, some 17⟩, -- 3.axiomcode.decnz / 0
  some ⟨true, true, some 47⟩, -- 3.axiomcode.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.axiomcode.inc / 0
  some ⟨true, true, some 48⟩, -- 3.axiomcode.inc / 1
  some ⟨false, true, some 17⟩, -- 3.nextproof.decnz / 0
  some ⟨true, true, some 39⟩, -- 3.nextproof.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.nextproof.inc / 0
  some ⟨true, true, some 40⟩, -- 3.nextproof.inc / 1
  some ⟨false, true, some 17⟩, -- 3.param1.decnz / 0
  some ⟨true, true, some 29⟩, -- 3.param1.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.param1.inc / 0
  some ⟨true, true, some 30⟩, -- 3.param1.inc / 1
  some ⟨false, true, some 17⟩, -- 3.param2.decnz / 0
  some ⟨true, true, some 33⟩, -- 3.param2.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.param2.inc / 0
  some ⟨true, true, some 34⟩, -- 3.param2.inc / 1
  some ⟨false, true, some 17⟩, -- 3.param3.decnz / 0
  some ⟨true, true, some 35⟩, -- 3.param3.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.param3.inc / 0
  some ⟨true, true, some 36⟩, -- 3.param3.inc / 1
  some ⟨false, true, some 17⟩, -- 3.prooflist.decnz / 0
  some ⟨true, true, some 5⟩, -- 3.prooflist.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.prooflist.inc / 0
  some ⟨true, true, some 13⟩, -- 3.prooflist.inc / 1
  some ⟨false, true, some 17⟩, -- 3.scratch1.decnz / 0
  some ⟨true, true, some 37⟩, -- 3.scratch1.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.scratch1.inc / 0
  some ⟨true, true, some 38⟩, -- 3.scratch1.inc / 1
  some ⟨false, true, some 17⟩, -- 3.scratch2.decnz / 0
  some ⟨true, true, some 41⟩, -- 3.scratch2.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.scratch2.inc / 0
  some ⟨true, true, some 42⟩, -- 3.scratch2.inc / 1
  some ⟨false, true, some 17⟩, -- 3.topwff.decnz / 0
  some ⟨true, true, some 31⟩, -- 3.topwff.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.topwff.inc / 0
  some ⟨true, true, some 32⟩, -- 3.topwff.inc / 1
  some ⟨false, true, some 17⟩, -- 3.wffstack.decnz / 0
  some ⟨true, true, some 45⟩, -- 3.wffstack.decnz / 1
  some ⟨false, true, some 17⟩, -- 3.wffstack.inc / 0
  some ⟨true, true, some 46⟩, -- 3.wffstack.inc / 1
  some ⟨false, false, some 50⟩, -- 4.dispatch.1 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.1 / 1
  some ⟨false, false, some 51⟩, -- 4.dispatch.2 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.2 / 1
  some ⟨false, false, some 52⟩, -- 4.dispatch.3 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.3 / 1
  some ⟨false, false, some 53⟩, -- 4.dispatch.4 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.4 / 1
  some ⟨false, false, some 54⟩, -- 4.dispatch.5 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.5 / 1
  some ⟨false, false, some 55⟩, -- 4.dispatch.6 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.6 / 1
  some ⟨false, true, some 56⟩, -- 4.dispatch.7 / 0
  some ⟨true, false, some 60⟩, -- 4.dispatch.7 / 1
  some ⟨false, true, some 56⟩, -- 5.root / 0
  some ⟨true, true, some 65⟩, -- 5.root / 1
  some ⟨true, false, some 60⟩, -- 6.break.0 / 0
  some ⟨false, false, some 57⟩, -- 6.break.0 / 1
  some ⟨false, false, some 57⟩, -- 6.break.1 / 0
  some ⟨false, false, some 58⟩, -- 6.break.1 / 1
  some ⟨false, false, some 58⟩, -- 6.break.2 / 0
  some ⟨false, false, some 59⟩, -- 6.break.2 / 1
  some ⟨false, false, some 49⟩, -- 6.continue.0 / 0
  some ⟨true, false, some 60⟩, -- 6.continue.0 / 1
  some ⟨false, false, some 61⟩, -- 6.continue.1 / 0
  some ⟨false, false, some 60⟩, -- 6.continue.1 / 1
  some ⟨false, false, some 62⟩, -- 6.continue.2 / 0
  some ⟨false, false, some 61⟩, -- 6.continue.2 / 1
  some ⟨false, false, some 63⟩, -- 6.continue.3 / 0
  some ⟨false, false, some 62⟩, -- 6.continue.3 / 1
  some ⟨false, false, some 64⟩, -- 6.continue.4 / 0
  some ⟨false, false, some 63⟩, -- 6.continue.4 / 1
  some ⟨false, true, some 66⟩, -- main().0 / 0
  some ⟨true, true, some 74⟩, -- main().0 / 1
  some ⟨false, true, some 67⟩, -- main().0.0 / 0
  some ⟨true, true, some 68⟩, -- main().0.0 / 1
  some ⟨false, true, some 39⟩, -- main().0.0.0 / 0
  some ⟨false, false, some 58⟩, -- main().0.0.0 / 1
  some ⟨false, true, some 69⟩, -- main().0.1 / 0
  some ⟨true, true, some 32⟩, -- main().0.1 / 1
  some ⟨false, true, some 70⟩, -- main().0.1.0 / 0
  some ⟨true, true, some 72⟩, -- main().0.1.0 / 1
  some ⟨false, true, some 31⟩, -- main().0.1.0.0 / 0
  some ⟨true, true, some 71⟩, -- main().0.1.0.0 / 1
  some ⟨false, true, some 40⟩, -- main().0.1.0.1 / 0
  some ⟨true, true, some 184⟩, -- main().0.1.0.1 / 1
  some ⟨false, true, some 41⟩, -- main().0.1.1 / 0
  some ⟨true, true, some 73⟩, -- main().0.1.1 / 1
  some ⟨false, true, some 32⟩, -- main().0.1.2 / 0
  some ⟨false, false, some 61⟩, -- main().0.1.2 / 1
  some ⟨false, true, some 191⟩, -- main().1 / 0
  some ⟨true, true, some 85⟩, -- main().1 / 1
  some ⟨false, true, some 233⟩, -- main().10 / 0
  some ⟨true, true, some 76⟩, -- main().10 / 1
  some ⟨false, true, some 237⟩, -- main().11 / 0
  some ⟨true, true, some 77⟩, -- main().11 / 1
  some ⟨false, true, some 254⟩, -- main().12 / 0
  some ⟨true, true, some 78⟩, -- main().12 / 1
  some ⟨false, true, some 260⟩, -- main().13 / 0
  some ⟨true, true, some 79⟩, -- main().13 / 1
  some ⟨false, true, some 261⟩, -- main().14 / 0
  some ⟨true, true, some 80⟩, -- main().14 / 1
  some ⟨false, true, some 263⟩, -- main().15 / 0
  some ⟨true, true, some 81⟩, -- main().15 / 1
  some ⟨false, true, some 265⟩, -- main().16 / 0
  some ⟨true, true, some 82⟩, -- main().16 / 1
  some ⟨false, true, some 243⟩, -- main().17 / 0
  some ⟨true, true, some 83⟩, -- main().17 / 1
  some ⟨false, true, some 263⟩, -- main().18 / 0
  some ⟨true, true, some 84⟩, -- main().18 / 1
  some ⟨false, true, some 233⟩, -- main().19 / 0
  some ⟨true, true, some 87⟩, -- main().19 / 1
  some ⟨false, true, some 86⟩, -- main().2 / 0
  some ⟨true, true, some 98⟩, -- main().2 / 1
  some ⟨false, true, some 33⟩, -- main().2.0 / 0
  some ⟨false, false, some 60⟩, -- main().2.0 / 1
  some ⟨false, true, some 267⟩, -- main().20 / 0
  some ⟨true, true, some 88⟩, -- main().20 / 1
  some ⟨false, true, some 269⟩, -- main().21 / 0
  some ⟨true, true, some 89⟩, -- main().21 / 1
  some ⟨false, true, some 243⟩, -- main().22 / 0
  some ⟨true, true, some 90⟩, -- main().22 / 1
  some ⟨false, true, some 271⟩, -- main().23 / 0
  some ⟨true, true, some 91⟩, -- main().23 / 1
  some ⟨false, true, some 253⟩, -- main().24 / 0
  some ⟨true, true, some 92⟩, -- main().24 / 1
  some ⟨false, true, some 225⟩, -- main().25 / 0
  some ⟨true, true, some 93⟩, -- main().25 / 1
  some ⟨false, true, some 265⟩, -- main().26 / 0
  some ⟨true, true, some 94⟩, -- main().26 / 1
  some ⟨false, true, some 280⟩, -- main().27 / 0
  some ⟨true, true, some 95⟩, -- main().27 / 1
  some ⟨false, true, some 96⟩, -- main().28 / 0
  some ⟨true, true, some 97⟩, -- main().28 / 1
  some ⟨false, true, some 272⟩, -- main().28.0 / 0
  some ⟨true, true, some 203⟩, -- main().28.0 / 1
  some ⟨false, true, some 271⟩, -- main().29 / 0
  some ⟨true, true, some 99⟩, -- main().29 / 1
  some ⟨false, true, some 195⟩, -- main().3 / 0
  some ⟨true, true, some 113⟩, -- main().3 / 1
  some ⟨false, true, some 100⟩, -- main().30 / 0
  some ⟨true, true, some 103⟩, -- main().30 / 1
  some ⟨false, true, some 101⟩, -- main().30.0 / 0
  some ⟨true, true, some 102⟩, -- main().30.0 / 1
  some ⟨false, true, some 45⟩, -- main().30.0.0 / 0
  some ⟨true, true, some 186⟩, -- main().30.0.0 / 1
  some ⟨false, true, some 282⟩, -- main().30.1 / 0
  some ⟨true, true, some 221⟩, -- main().30.1 / 1
  some ⟨false, true, some 104⟩, -- main().31 / 0
  some ⟨true, true, some 105⟩, -- main().31 / 1
  some ⟨false, true, some 292⟩, -- main().31.0 / 0
  some ⟨true, true, some 233⟩, -- main().31.0 / 1
  some ⟨false, true, some 266⟩, -- main().32 / 0
  some ⟨true, true, some 106⟩, -- main().32 / 1
  some ⟨false, true, some 232⟩, -- main().33 / 0
  some ⟨true, true, some 107⟩, -- main().33 / 1
  some ⟨false, true, some 253⟩, -- main().34 / 0
  some ⟨true, true, some 108⟩, -- main().34 / 1
  some ⟨false, true, some 237⟩, -- main().35 / 0
  some ⟨true, true, some 109⟩, -- main().35 / 1
  some ⟨false, true, some 293⟩, -- main().36 / 0
  some ⟨true, true, some 110⟩, -- main().36 / 1
  some ⟨false, true, some 260⟩, -- main().37 / 0
  some ⟨true, true, some 111⟩, -- main().37 / 1
  some ⟨false, true, some 240⟩, -- main().38 / 0
  some ⟨true, true, some 112⟩, -- main().38 / 1
  some ⟨false, true, some 258⟩, -- main().39 / 0
  some ⟨true, true, some 114⟩, -- main().39 / 1
  some ⟨false, true, some 191⟩, -- main().4 / 0
  some ⟨true, true, some 124⟩, -- main().4 / 1
  some ⟨false, true, some 280⟩, -- main().40 / 0
  some ⟨true, true, some 115⟩, -- main().40 / 1
  some ⟨false, true, some 294⟩, -- main().41 / 0
  some ⟨true, true, some 116⟩, -- main().41 / 1
  some ⟨false, true, some 292⟩, -- main().42 / 0
  some ⟨true, true, some 117⟩, -- main().42 / 1
  some ⟨false, true, some 256⟩, -- main().43 / 0
  some ⟨true, true, some 118⟩, -- main().43 / 1
  some ⟨false, true, some 254⟩, -- main().44 / 0
  some ⟨true, true, some 119⟩, -- main().44 / 1
  some ⟨false, true, some 294⟩, -- main().45 / 0
  some ⟨true, true, some 120⟩, -- main().45 / 1
  some ⟨false, true, some 295⟩, -- main().46 / 0
  some ⟨true, true, some 121⟩, -- main().46 / 1
  some ⟨false, true, some 234⟩, -- main().47 / 0
  some ⟨true, true, some 122⟩, -- main().47 / 1
  some ⟨false, true, some 258⟩, -- main().48 / 0
  some ⟨true, true, some 123⟩, -- main().48 / 1
  some ⟨false, true, some 296⟩, -- main().49 / 0
  some ⟨true, true, some 125⟩, -- main().49 / 1
  some ⟨false, true, some 199⟩, -- main().5 / 0
  some ⟨true, true, some 144⟩, -- main().5 / 1
  some ⟨false, true, some 215⟩, -- main().50 / 0
  some ⟨true, true, some 126⟩, -- main().50 / 1
  some ⟨false, true, some 127⟩, -- main().51 / 0
  some ⟨true, true, some 131⟩, -- main().51 / 1
  some ⟨false, true, some 128⟩, -- main().51.0 / 0
  some ⟨true, true, some 129⟩, -- main().51.0 / 1
  some ⟨false, true, some 33⟩, -- main().51.0.0 / 0
  some ⟨true, true, some 205⟩, -- main().51.0.0 / 1
  some ⟨false, true, some 130⟩, -- main().51.1 / 0
  some ⟨true, true, some 34⟩, -- main().51.1 / 1
  some ⟨false, true, some 195⟩, -- main().51.1.0 / 0
  some ⟨true, true, some 282⟩, -- main().51.1.0 / 1
  some ⟨false, true, some 132⟩, -- main().52 / 0
  some ⟨true, true, some 136⟩, -- main().52 / 1
  some ⟨false, true, some 133⟩, -- main().52.0 / 0
  some ⟨true, true, some 134⟩, -- main().52.0 / 1
  some ⟨false, true, some 37⟩, -- main().52.0.0 / 0
  some ⟨true, true, some 205⟩, -- main().52.0.0 / 1
  some ⟨false, true, some 197⟩, -- main().52.1 / 0
  some ⟨true, true, some 135⟩, -- main().52.1 / 1
  some ⟨false, true, some 282⟩, -- main().52.2 / 0
  some ⟨true, true, some 38⟩, -- main().52.2 / 1
  some ⟨false, true, some 228⟩, -- main().53 / 0
  some ⟨true, true, some 137⟩, -- main().53 / 1
  some ⟨false, true, some 207⟩, -- main().54 / 0
  some ⟨true, true, some 138⟩, -- main().54 / 1
  some ⟨false, true, some 139⟩, -- main().55 / 0
  some ⟨true, true, some 140⟩, -- main().55 / 1
  some ⟨false, true, some 297⟩, -- main().55.0 / 0
  some ⟨true, true, some 225⟩, -- main().55.0 / 1
  some ⟨false, true, some 297⟩, -- main().56 / 0
  some ⟨true, true, some 141⟩, -- main().56 / 1
  some ⟨false, true, some 296⟩, -- main().57 / 0
  some ⟨true, true, some 142⟩, -- main().57 / 1
  some ⟨false, true, some 298⟩, -- main().58 / 0
  some ⟨true, true, some 143⟩, -- main().58 / 1
  some ⟨false, true, some 300⟩, -- main().59 / 0
  some ⟨true, true, some 145⟩, -- main().59 / 1
  some ⟨false, true, some 191⟩, -- main().6 / 0
  some ⟨true, true, some 155⟩, -- main().6 / 1
  some ⟨false, true, some 302⟩, -- main().60 / 0
  some ⟨true, true, some 146⟩, -- main().60 / 1
  some ⟨false, true, some 303⟩, -- main().61 / 0
  some ⟨true, true, some 147⟩, -- main().61 / 1
  some ⟨false, true, some 234⟩, -- main().62 / 0
  some ⟨true, true, some 148⟩, -- main().62 / 1
  some ⟨false, true, some 266⟩, -- main().63 / 0
  some ⟨true, true, some 149⟩, -- main().63 / 1
  some ⟨false, true, some 239⟩, -- main().64 / 0
  some ⟨true, true, some 150⟩, -- main().64 / 1
  some ⟨false, true, some 300⟩, -- main().65 / 0
  some ⟨true, true, some 151⟩, -- main().65 / 1
  some ⟨false, true, some 293⟩, -- main().66 / 0
  some ⟨true, true, some 152⟩, -- main().66 / 1
  some ⟨false, true, some 303⟩, -- main().67 / 0
  some ⟨true, true, some 153⟩, -- main().67 / 1
  some ⟨false, true, some 241⟩, -- main().68 / 0
  some ⟨true, true, some 154⟩, -- main().68 / 1
  some ⟨false, true, some 305⟩, -- main().69 / 0
  some ⟨true, true, some 156⟩, -- main().69 / 1
  some ⟨false, true, some 203⟩, -- main().7 / 0
  some ⟨true, true, some 168⟩, -- main().7 / 1
  some ⟨false, true, some 157⟩, -- main().70 / 0
  some ⟨true, true, some 158⟩, -- main().70 / 1
  some ⟨false, true, some 269⟩, -- main().70.0 / 0
  some ⟨true, true, some 239⟩, -- main().70.0 / 1
  some ⟨false, true, some 305⟩, -- main().71 / 0
  some ⟨true, true, some 159⟩, -- main().71 / 1
  some ⟨false, true, some 241⟩, -- main().72 / 0
  some ⟨true, true, some 160⟩, -- main().72 / 1
  some ⟨false, true, some 243⟩, -- main().73 / 0
  some ⟨true, true, some 161⟩, -- main().73 / 1
  some ⟨false, true, some 162⟩, -- main().74 / 0
  some ⟨true, true, some 163⟩, -- main().74 / 1
  some ⟨false, true, some 306⟩, -- main().74.0 / 0
  some ⟨true, true, some 306⟩, -- main().74.0 / 1
  some ⟨false, true, some 295⟩, -- main().75 / 0
  some ⟨true, true, some 164⟩, -- main().75 / 1
  some ⟨false, true, some 298⟩, -- main().76 / 0
  some ⟨true, true, some 165⟩, -- main().76 / 1
  some ⟨false, true, some 307⟩, -- main().77 / 0
  some ⟨true, true, some 166⟩, -- main().77 / 1
  some ⟨false, true, some 297⟩, -- main().78 / 0
  some ⟨true, true, some 167⟩, -- main().78 / 1
  some ⟨false, true, some 307⟩, -- main().79 / 0
  some ⟨true, true, some 169⟩, -- main().79 / 1
  some ⟨false, true, some 191⟩, -- main().8 / 0
  some ⟨true, true, some 178⟩, -- main().8 / 1
  some ⟨false, true, some 292⟩, -- main().80 / 0
  some ⟨true, true, some 170⟩, -- main().80 / 1
  some ⟨false, true, some 171⟩, -- main().81 / 0
  some ⟨true, true, some 172⟩, -- main().81 / 1
  some ⟨false, true, some 225⟩, -- main().81.0 / 0
  some ⟨true, true, some 291⟩, -- main().81.0 / 1
  some ⟨false, true, some 296⟩, -- main().82 / 0
  some ⟨true, true, some 173⟩, -- main().82 / 1
  some ⟨false, true, some 45⟩, -- main().83 / 0
  some ⟨true, true, some 174⟩, -- main().83 / 1
  some ⟨false, true, some 175⟩, -- main().84 / 0
  some ⟨true, true, none⟩, -- main().84 / 1
  some ⟨false, true, some 45⟩, -- main().84.0 / 0
  some ⟨true, true, some 176⟩, -- main().84.0 / 1
  some ⟨false, true, some 177⟩, -- main().84.1 / 0
  some ⟨false, false, some 58⟩, -- main().84.1 / 1
  some ⟨false, true, some 46⟩, -- main().84.1.0 / 0
  some ⟨true, true, some 46⟩, -- main().84.1.0 / 1
  some ⟨false, true, some 179⟩, -- main().9 / 0
  some ⟨true, true, some 75⟩, -- main().9 / 1
  some ⟨false, true, some 180⟩, -- main().9.0 / 0
  some ⟨true, true, some 181⟩, -- main().9.0 / 1
  some ⟨false, true, some 29⟩, -- main().9.0.0 / 0
  some ⟨false, false, some 60⟩, -- main().9.0.0 / 1
  some ⟨false, true, some 182⟩, -- main().9.1 / 0
  some ⟨true, true, some 215⟩, -- main().9.1 / 1
  some ⟨false, true, some 41⟩, -- main().9.1.0 / 0
  some ⟨true, true, some 183⟩, -- main().9.1.0 / 1
  some ⟨false, true, some 30⟩, -- main().9.1.1 / 0
  some ⟨false, false, some 61⟩, -- main().9.1.1 / 1
  some ⟨false, true, some 42⟩, -- main().n_001.0 / 0
  some ⟨false, false, some 62⟩, -- main().n_001.0 / 1
  some ⟨false, true, some 43⟩, -- main().n_009.0 / 0
  some ⟨false, false, some 62⟩, -- main().n_009.0 / 1
  some ⟨false, true, some 44⟩, -- main().n_010.0 / 0
  some ⟨false, false, some 61⟩, -- main().n_010.0 / 1
  some ⟨false, true, some 41⟩, -- main().n_011.0 / 0
  some ⟨true, true, some 186⟩, -- main().n_011.0 / 1
  some ⟨false, true, some 187⟩, -- main().n_012.0 / 0
  some ⟨false, false, some 63⟩, -- main().n_012.0 / 1
  some ⟨false, true, some 185⟩, -- main().n_013.0 / 0
  some ⟨true, true, some 188⟩, -- main().n_013.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_014.0 / 0
  some ⟨true, true, some 189⟩, -- main().n_014.0 / 1
  some ⟨false, true, some 192⟩, -- main().n_018.0 / 0
  some ⟨true, true, some 193⟩, -- main().n_018.0 / 1
  some ⟨false, true, some 39⟩, -- main().n_018.0.0 / 0
  some ⟨true, true, some 190⟩, -- main().n_018.0.0 / 1
  some ⟨false, true, some 43⟩, -- main().n_018.1 / 0
  some ⟨true, true, some 194⟩, -- main().n_018.1 / 1
  some ⟨false, true, some 40⟩, -- main().n_018.2 / 0
  some ⟨false, false, some 61⟩, -- main().n_018.2 / 1
  some ⟨false, true, some 41⟩, -- main().n_021.0 / 0
  some ⟨true, true, some 196⟩, -- main().n_021.0 / 1
  some ⟨false, true, some 34⟩, -- main().n_021.1 / 0
  some ⟨false, false, some 61⟩, -- main().n_021.1 / 1
  some ⟨false, true, some 41⟩, -- main().n_024.0 / 0
  some ⟨true, true, some 198⟩, -- main().n_024.0 / 1
  some ⟨false, true, some 38⟩, -- main().n_024.1 / 0
  some ⟨false, false, some 61⟩, -- main().n_024.1 / 1
  some ⟨false, true, some 200⟩, -- main().n_025.0 / 0
  some ⟨true, true, some 197⟩, -- main().n_025.0 / 1
  some ⟨false, true, some 37⟩, -- main().n_025.0.0 / 0
  some ⟨false, false, some 60⟩, -- main().n_025.0.0 / 1
  some ⟨false, true, some 41⟩, -- main().n_028.0 / 0
  some ⟨true, true, some 202⟩, -- main().n_028.0 / 1
  some ⟨false, true, some 36⟩, -- main().n_028.1 / 0
  some ⟨false, false, some 61⟩, -- main().n_028.1 / 1
  some ⟨false, true, some 204⟩, -- main().n_029.0 / 0
  some ⟨true, true, some 201⟩, -- main().n_029.0 / 1
  some ⟨false, true, some 35⟩, -- main().n_029.0.0 / 0
  some ⟨false, false, some 60⟩, -- main().n_029.0.0 / 1
  some ⟨false, true, some 44⟩, -- main().n_035.0 / 0
  some ⟨true, true, some 184⟩, -- main().n_035.0 / 1
  some ⟨false, true, some 46⟩, -- main().n_037.0 / 0
  some ⟨false, false, some 61⟩, -- main().n_037.0 / 1
  some ⟨false, true, some 41⟩, -- main().n_038.0 / 0
  some ⟨true, true, some 206⟩, -- main().n_038.0 / 1
  some ⟨false, true, some 209⟩, -- main().n_042.0 / 0
  some ⟨true, true, some 210⟩, -- main().n_042.0 / 1
  some ⟨false, true, some 45⟩, -- main().n_042.0.0 / 0
  some ⟨true, true, some 205⟩, -- main().n_042.0.0 / 1
  some ⟨false, true, some 41⟩, -- main().n_042.1 / 0
  some ⟨true, true, some 211⟩, -- main().n_042.1 / 1
  some ⟨false, true, some 44⟩, -- main().n_042.2 / 0
  some ⟨true, true, some 212⟩, -- main().n_042.2 / 1
  some ⟨false, true, some 207⟩, -- main().n_042.3 / 0
  some ⟨false, false, some 63⟩, -- main().n_042.3 / 1
  some ⟨false, true, some 43⟩, -- main().n_044.0 / 0
  some ⟨true, true, some 214⟩, -- main().n_044.0 / 1
  some ⟨false, true, some 48⟩, -- main().n_044.1 / 0
  some ⟨false, false, some 61⟩, -- main().n_044.1 / 1
  some ⟨false, true, some 216⟩, -- main().n_046.0 / 0
  some ⟨true, true, some 218⟩, -- main().n_046.0 / 1
  some ⟨false, true, some 47⟩, -- main().n_046.0.0 / 0
  some ⟨true, true, some 217⟩, -- main().n_046.0.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_046.0.1 / 0
  some ⟨false, false, some 61⟩, -- main().n_046.0.1 / 1
  some ⟨false, true, some 208⟩, -- main().n_046.1 / 0
  some ⟨true, true, some 213⟩, -- main().n_046.1 / 1
  some ⟨false, true, some 46⟩, -- main().n_049.0 / 0
  some ⟨true, true, some 184⟩, -- main().n_049.0 / 1
  some ⟨false, true, some 33⟩, -- main().n_050.0 / 0
  some ⟨true, true, some 219⟩, -- main().n_050.0 / 1
  some ⟨false, true, some 220⟩, -- main().n_051.0 / 0
  some ⟨true, true, some 195⟩, -- main().n_051.0 / 1
  some ⟨false, true, some 215⟩, -- main().n_052.0 / 0
  some ⟨true, true, some 221⟩, -- main().n_052.0 / 1
  some ⟨false, true, some 35⟩, -- main().n_053.0 / 0
  some ⟨true, true, some 219⟩, -- main().n_053.0 / 1
  some ⟨false, true, some 223⟩, -- main().n_054.0 / 0
  some ⟨true, true, some 201⟩, -- main().n_054.0 / 1
  some ⟨false, true, some 215⟩, -- main().n_055.0 / 0
  some ⟨true, true, some 224⟩, -- main().n_055.0 / 1
  some ⟨false, true, some 222⟩, -- main().n_056.0 / 0
  some ⟨true, true, some 225⟩, -- main().n_056.0 / 1
  some ⟨false, true, some 47⟩, -- main().n_057.0 / 0
  some ⟨true, true, some 190⟩, -- main().n_057.0 / 1
  some ⟨false, true, some 227⟩, -- main().n_058.0 / 0
  some ⟨true, true, some 213⟩, -- main().n_058.0 / 1
  some ⟨false, true, some 208⟩, -- main().n_060.0 / 0
  some ⟨true, true, some 230⟩, -- main().n_060.0 / 1
  some ⟨false, true, some 43⟩, -- main().n_060.1 / 0
  some ⟨true, true, some 206⟩, -- main().n_060.1 / 1
  some ⟨false, true, some 228⟩, -- main().n_061.0 / 0
  some ⟨true, true, some 229⟩, -- main().n_061.0 / 1
  some ⟨false, true, some 231⟩, -- main().n_062.0 / 0
  some ⟨true, true, some 229⟩, -- main().n_062.0 / 1
  some ⟨false, true, some 226⟩, -- main().n_063.0 / 0
  some ⟨true, true, some 232⟩, -- main().n_063.0 / 1
  some ⟨false, true, some 215⟩, -- main().n_066.0 / 0
  some ⟨true, true, some 235⟩, -- main().n_066.0 / 1
  some ⟨false, true, some 236⟩, -- main().n_066.1 / 0
  some ⟨true, true, some 197⟩, -- main().n_066.1 / 1
  some ⟨false, true, some 37⟩, -- main().n_066.1.0 / 0
  some ⟨true, true, some 219⟩, -- main().n_066.1.0 / 1
  some ⟨false, true, some 222⟩, -- main().n_067.0 / 0
  some ⟨true, true, some 234⟩, -- main().n_067.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_068.0 / 0
  some ⟨true, true, some 229⟩, -- main().n_068.0 / 1
  some ⟨false, true, some 231⟩, -- main().n_069.0 / 0
  some ⟨true, true, some 238⟩, -- main().n_069.0 / 1
  some ⟨false, true, some 225⟩, -- main().n_070.0 / 0
  some ⟨true, true, some 234⟩, -- main().n_070.0 / 1
  some ⟨false, true, some 240⟩, -- main().n_071.0 / 0
  some ⟨true, true, some 239⟩, -- main().n_071.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_072.0 / 0
  some ⟨true, true, some 238⟩, -- main().n_072.0 / 1
  some ⟨false, true, some 231⟩, -- main().n_073.0 / 0
  some ⟨true, true, some 242⟩, -- main().n_073.0 / 1
  some ⟨false, true, some 29⟩, -- main().n_074.0 / 0
  some ⟨false, false, some 58⟩, -- main().n_074.0 / 1
  some ⟨false, true, some 45⟩, -- main().n_075.0 / 0
  some ⟨false, false, some 60⟩, -- main().n_075.0 / 1
  some ⟨false, true, some 245⟩, -- main().n_076.0 / 0
  some ⟨true, true, some 207⟩, -- main().n_076.0 / 1
  some ⟨false, true, some 244⟩, -- main().n_077.0 / 0
  some ⟨true, true, some 246⟩, -- main().n_077.0 / 1
  some ⟨false, true, some 228⟩, -- main().n_078.0 / 0
  some ⟨true, true, some 247⟩, -- main().n_078.0 / 1
  some ⟨false, true, some 41⟩, -- main().n_079.0 / 0
  some ⟨false, false, some 60⟩, -- main().n_079.0 / 1
  some ⟨false, true, some 248⟩, -- main().n_080.0 / 0
  some ⟨true, true, some 249⟩, -- main().n_080.0 / 1
  some ⟨false, true, some 243⟩, -- main().n_081.0 / 0
  some ⟨true, true, some 250⟩, -- main().n_081.0 / 1
  some ⟨false, true, some 243⟩, -- main().n_082.0 / 0
  some ⟨true, true, some 251⟩, -- main().n_082.0 / 1
  some ⟨false, true, some 252⟩, -- main().n_083.0 / 0
  some ⟨true, true, some 225⟩, -- main().n_083.0 / 1
  some ⟨false, true, some 239⟩, -- main().n_085.0 / 0
  some ⟨true, true, some 255⟩, -- main().n_085.0 / 1
  some ⟨false, true, some 241⟩, -- main().n_085.1 / 0
  some ⟨true, true, some 253⟩, -- main().n_085.1 / 1
  some ⟨false, true, some 225⟩, -- main().n_086.0 / 0
  some ⟨true, true, some 222⟩, -- main().n_086.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_087.0 / 0
  some ⟨true, true, some 242⟩, -- main().n_087.0 / 1
  some ⟨false, true, some 231⟩, -- main().n_089.0 / 0
  some ⟨true, true, some 259⟩, -- main().n_089.0 / 1
  some ⟨false, true, some 42⟩, -- main().n_089.1 / 0
  some ⟨true, true, some 257⟩, -- main().n_089.1 / 1
  some ⟨false, true, some 256⟩, -- main().n_090.0 / 0
  some ⟨true, true, some 258⟩, -- main().n_090.0 / 1
  some ⟨false, true, some 257⟩, -- main().n_092.0 / 0
  some ⟨true, true, some 262⟩, -- main().n_092.0 / 1
  some ⟨false, true, some 258⟩, -- main().n_092.1 / 0
  some ⟨true, true, some 257⟩, -- main().n_092.1 / 1
  some ⟨false, true, some 222⟩, -- main().n_094.0 / 0
  some ⟨true, true, some 264⟩, -- main().n_094.0 / 1
  some ⟨false, true, some 251⟩, -- main().n_094.1 / 0
  some ⟨true, true, some 222⟩, -- main().n_094.1 / 1
  some ⟨false, true, some 257⟩, -- main().n_095.0 / 0
  some ⟨true, true, some 222⟩, -- main().n_095.0 / 1
  some ⟨false, true, some 234⟩, -- main().n_097.0 / 0
  some ⟨true, true, some 225⟩, -- main().n_097.0 / 1
  some ⟨false, true, some 268⟩, -- main().n_098.0 / 0
  some ⟨true, true, some 266⟩, -- main().n_098.0 / 1
  some ⟨false, true, some 261⟩, -- main().n_098.0.0 / 0
  some ⟨true, true, some 250⟩, -- main().n_098.0.0 / 1
  some ⟨false, true, some 243⟩, -- main().n_099.0 / 0
  some ⟨true, true, some 256⟩, -- main().n_099.0 / 1
  some ⟨false, true, some 234⟩, -- main().n_100.0 / 0
  some ⟨true, true, some 222⟩, -- main().n_100.0 / 1
  some ⟨false, true, some 270⟩, -- main().n_101.0 / 0
  some ⟨true, true, some 243⟩, -- main().n_101.0 / 1
  some ⟨false, true, some 273⟩, -- main().n_109.0 / 0
  some ⟨false, false, some 58⟩, -- main().n_109.0 / 1
  some ⟨false, true, some 29⟩, -- main().n_109.0.0 / 0
  some ⟨true, true, some 274⟩, -- main().n_109.0.0 / 1
  some ⟨false, true, some 275⟩, -- main().n_109.0.1 / 0
  some ⟨true, true, some 278⟩, -- main().n_109.0.1 / 1
  some ⟨false, true, some 29⟩, -- main().n_109.0.1.0 / 0
  some ⟨true, true, some 276⟩, -- main().n_109.0.1.0 / 1
  some ⟨false, true, some 277⟩, -- main().n_109.0.1.1 / 0
  some ⟨false, false, some 58⟩, -- main().n_109.0.1.1 / 1
  some ⟨false, true, some 30⟩, -- main().n_109.0.1.1.0 / 0
  some ⟨true, true, some 30⟩, -- main().n_109.0.1.1.0 / 1
  some ⟨false, true, some 30⟩, -- main().n_109.0.2 / 0
  some ⟨true, true, some 279⟩, -- main().n_109.0.2 / 1
  some ⟨false, true, some 228⟩, -- main().n_109.0.3 / 0
  some ⟨false, false, some 58⟩, -- main().n_109.0.3 / 1
  some ⟨false, true, some 252⟩, -- main().n_111.0 / 0
  some ⟨true, true, some 281⟩, -- main().n_111.0 / 1
  some ⟨false, true, some 272⟩, -- main().n_111.1 / 0
  some ⟨true, true, some 199⟩, -- main().n_111.1 / 1
  some ⟨false, true, some 283⟩, -- main().n_122.0 / 0
  some ⟨true, true, some 289⟩, -- main().n_122.0 / 1
  some ⟨false, true, some 224⟩, -- main().n_122.0.0 / 0
  some ⟨true, true, some 284⟩, -- main().n_122.0.0 / 1
  some ⟨false, true, some 43⟩, -- main().n_122.0.1 / 0
  some ⟨true, true, some 285⟩, -- main().n_122.0.1 / 1
  some ⟨false, true, some 286⟩, -- main().n_122.0.2 / 0
  some ⟨true, true, some 287⟩, -- main().n_122.0.2 / 1
  some ⟨false, true, some 45⟩, -- main().n_122.0.2.0 / 0
  some ⟨false, false, some 61⟩, -- main().n_122.0.2.0 / 1
  some ⟨false, true, some 288⟩, -- main().n_122.0.3 / 0
  some ⟨false, false, some 59⟩, -- main().n_122.0.3 / 1
  some ⟨false, true, some 43⟩, -- main().n_122.0.3.0 / 0
  some ⟨false, false, some 60⟩, -- main().n_122.0.3.0 / 1
  some ⟨false, true, some 45⟩, -- main().n_122.1 / 0
  some ⟨true, true, some 290⟩, -- main().n_122.1 / 1
  some ⟨false, true, some 245⟩, -- main().n_122.2 / 0
  some ⟨false, false, some 58⟩, -- main().n_122.2 / 1
  some ⟨false, true, some 237⟩, -- main().n_125.0 / 0
  some ⟨true, true, some 232⟩, -- main().n_125.0 / 1
  some ⟨false, true, some 250⟩, -- main().n_126.0 / 0
  some ⟨true, true, some 291⟩, -- main().n_126.0 / 1
  some ⟨false, true, some 243⟩, -- main().n_128.0 / 0
  some ⟨true, true, some 258⟩, -- main().n_128.0 / 1
  some ⟨false, true, some 237⟩, -- main().n_129.0 / 0
  some ⟨true, true, some 258⟩, -- main().n_129.0 / 1
  some ⟨false, true, some 258⟩, -- main().n_130.0 / 0
  some ⟨true, true, some 226⟩, -- main().n_130.0 / 1
  some ⟨false, true, some 258⟩, -- main().n_131.0 / 0
  some ⟨true, true, some 251⟩, -- main().n_131.0 / 1
  some ⟨false, true, some 237⟩, -- main().n_140.0 / 0
  some ⟨true, true, some 239⟩, -- main().n_140.0 / 1
  some ⟨false, true, some 266⟩, -- main().n_143.0 / 0
  some ⟨true, true, some 299⟩, -- main().n_143.0 / 1
  some ⟨false, true, some 234⟩, -- main().n_143.1 / 0
  some ⟨true, true, some 241⟩, -- main().n_143.1 / 1
  some ⟨false, true, some 270⟩, -- main().n_144.0 / 0
  some ⟨true, true, some 239⟩, -- main().n_144.0 / 1
  some ⟨false, true, some 257⟩, -- main().n_145.0 / 0
  some ⟨true, true, some 293⟩, -- main().n_145.0 / 1
  some ⟨false, true, some 301⟩, -- main().n_146.0 / 0
  some ⟨true, true, some 257⟩, -- main().n_146.0 / 1
  some ⟨false, true, some 241⟩, -- main().n_148.0 / 0
  some ⟨true, true, some 304⟩, -- main().n_148.0 / 1
  some ⟨false, true, some 293⟩, -- main().n_148.1 / 0
  some ⟨true, true, some 267⟩, -- main().n_148.1 / 1
  some ⟨false, true, some 237⟩, -- main().n_149.0 / 0
  some ⟨true, true, some 261⟩, -- main().n_149.0 / 1
  some ⟨false, true, some 243⟩, -- main().n_151.0 / 0
  some ⟨true, true, some 257⟩, -- main().n_151.0 / 1
  some ⟨false, true, some 301⟩, -- main().n_153.0 / 0
  some ⟨true, true, some 302⟩, -- main().n_153.0 / 1
], by decide⟩

/-- The literal machine, with no extra working states. -/
def machine : Machine 308 := fun q b => table.get ⟨2 * q.val + (if b then 1 else 0), by cases b <;> simp <;> omega⟩

/-- A balanced lookup used only to accelerate certificate evaluation.
 The semantic machine remains the literal table above. -/
def fastLookup : Machine 308 := fun q b =>
  if q.val < 154 then
    if q.val < 77 then
      if q.val < 38 then
        if q.val < 19 then
          if q.val < 9 then
            if q.val < 4 then
              if q.val < 2 then
                if q.val < 1 then
                  if b then some ⟨false, false, some 2⟩ else some ⟨true, true, some 1⟩
                else
                  if b then some ⟨false, true, some 1⟩ else some ⟨false, true, some 2⟩
              else
                if q.val < 3 then
                  if b then some ⟨false, true, some 4⟩ else some ⟨true, false, some 3⟩
                else
                  if b then some ⟨false, false, some 64⟩ else some ⟨false, false, some 4⟩
            else
              if q.val < 6 then
                if q.val < 5 then
                  if b then some ⟨false, false, some 1⟩ else some ⟨true, false, some 0⟩
                else
                  if b then some ⟨true, false, some 10⟩ else some ⟨true, true, some 6⟩
              else
                if q.val < 7 then
                  if b then some ⟨false, true, some 7⟩ else some ⟨false, true, some 6⟩
                else
                  if q.val < 8 then
                    if b then some ⟨true, true, some 7⟩ else some ⟨true, true, some 8⟩
                  else
                    if b then some ⟨false, true, some 7⟩ else some ⟨false, true, some 9⟩
          else
            if q.val < 14 then
              if q.val < 11 then
                if q.val < 10 then
                  if b then some ⟨true, true, some 9⟩ else some ⟨false, false, some 5⟩
                else
                  if b then some ⟨true, true, some 11⟩ else some ⟨false, false, some 26⟩
              else
                if q.val < 12 then
                  if b then some ⟨false, true, some 11⟩ else some ⟨true, true, some 12⟩
                else
                  if q.val < 13 then
                    if b then some ⟨true, true, some 9⟩ else some ⟨false, false, some 17⟩
                  else
                    if b then none else some ⟨true, true, some 14⟩
            else
              if q.val < 16 then
                if q.val < 15 then
                  if b then some ⟨true, true, some 15⟩ else some ⟨false, true, some 14⟩
                else
                  if b then some ⟨true, true, some 15⟩ else some ⟨false, true, some 16⟩
              else
                if q.val < 17 then
                  if b then some ⟨true, true, some 15⟩ else some ⟨true, false, some 23⟩
                else
                  if q.val < 18 then
                    if b then some ⟨false, false, some 23⟩ else some ⟨true, true, some 18⟩
                  else
                    if b then some ⟨true, true, some 19⟩ else some ⟨false, true, some 18⟩
        else
          if q.val < 28 then
            if q.val < 23 then
              if q.val < 21 then
                if q.val < 20 then
                  if b then some ⟨true, true, some 19⟩ else some ⟨false, true, some 20⟩
                else
                  if b then some ⟨true, true, some 19⟩ else some ⟨false, false, some 21⟩
              else
                if q.val < 22 then
                  if b then some ⟨false, false, some 23⟩ else some ⟨true, false, some 22⟩
                else
                  if b then some ⟨true, false, some 22⟩ else some ⟨false, true, some 21⟩
            else
              if q.val < 25 then
                if q.val < 24 then
                  if b then some ⟨true, false, some 23⟩ else some ⟨false, false, some 24⟩
                else
                  if b then some ⟨true, false, some 23⟩ else some ⟨false, false, some 25⟩
              else
                if q.val < 26 then
                  if b then some ⟨false, false, some 57⟩ else some ⟨false, false, some 25⟩
                else
                  if q.val < 27 then
                    if b then some ⟨true, false, some 26⟩ else some ⟨false, false, some 27⟩
                  else
                    if b then some ⟨true, false, some 26⟩ else some ⟨false, false, some 28⟩
          else
            if q.val < 33 then
              if q.val < 30 then
                if q.val < 29 then
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, false, some 28⟩
                else
                  if b then some ⟨true, true, some 47⟩ else some ⟨false, true, some 17⟩
              else
                if q.val < 31 then
                  if b then some ⟨true, true, some 48⟩ else some ⟨false, true, some 17⟩
                else
                  if q.val < 32 then
                    if b then some ⟨true, true, some 39⟩ else some ⟨false, true, some 17⟩
                  else
                    if b then some ⟨true, true, some 40⟩ else some ⟨false, true, some 17⟩
            else
              if q.val < 35 then
                if q.val < 34 then
                  if b then some ⟨true, true, some 29⟩ else some ⟨false, true, some 17⟩
                else
                  if b then some ⟨true, true, some 30⟩ else some ⟨false, true, some 17⟩
              else
                if q.val < 36 then
                  if b then some ⟨true, true, some 33⟩ else some ⟨false, true, some 17⟩
                else
                  if q.val < 37 then
                    if b then some ⟨true, true, some 34⟩ else some ⟨false, true, some 17⟩
                  else
                    if b then some ⟨true, true, some 35⟩ else some ⟨false, true, some 17⟩
      else
        if q.val < 57 then
          if q.val < 47 then
            if q.val < 42 then
              if q.val < 40 then
                if q.val < 39 then
                  if b then some ⟨true, true, some 36⟩ else some ⟨false, true, some 17⟩
                else
                  if b then some ⟨true, true, some 5⟩ else some ⟨false, true, some 17⟩
              else
                if q.val < 41 then
                  if b then some ⟨true, true, some 13⟩ else some ⟨false, true, some 17⟩
                else
                  if b then some ⟨true, true, some 37⟩ else some ⟨false, true, some 17⟩
            else
              if q.val < 44 then
                if q.val < 43 then
                  if b then some ⟨true, true, some 38⟩ else some ⟨false, true, some 17⟩
                else
                  if b then some ⟨true, true, some 41⟩ else some ⟨false, true, some 17⟩
              else
                if q.val < 45 then
                  if b then some ⟨true, true, some 42⟩ else some ⟨false, true, some 17⟩
                else
                  if q.val < 46 then
                    if b then some ⟨true, true, some 31⟩ else some ⟨false, true, some 17⟩
                  else
                    if b then some ⟨true, true, some 32⟩ else some ⟨false, true, some 17⟩
          else
            if q.val < 52 then
              if q.val < 49 then
                if q.val < 48 then
                  if b then some ⟨true, true, some 45⟩ else some ⟨false, true, some 17⟩
                else
                  if b then some ⟨true, true, some 46⟩ else some ⟨false, true, some 17⟩
              else
                if q.val < 50 then
                  if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 50⟩
                else
                  if q.val < 51 then
                    if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 51⟩
                  else
                    if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 52⟩
            else
              if q.val < 54 then
                if q.val < 53 then
                  if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 53⟩
                else
                  if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 54⟩
              else
                if q.val < 55 then
                  if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 55⟩
                else
                  if q.val < 56 then
                    if b then some ⟨true, false, some 60⟩ else some ⟨false, true, some 56⟩
                  else
                    if b then some ⟨true, true, some 65⟩ else some ⟨false, true, some 56⟩
        else
          if q.val < 67 then
            if q.val < 62 then
              if q.val < 59 then
                if q.val < 58 then
                  if b then some ⟨false, false, some 57⟩ else some ⟨true, false, some 60⟩
                else
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, false, some 57⟩
              else
                if q.val < 60 then
                  if b then some ⟨false, false, some 59⟩ else some ⟨false, false, some 58⟩
                else
                  if q.val < 61 then
                    if b then some ⟨true, false, some 60⟩ else some ⟨false, false, some 49⟩
                  else
                    if b then some ⟨false, false, some 60⟩ else some ⟨false, false, some 61⟩
            else
              if q.val < 64 then
                if q.val < 63 then
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, false, some 62⟩
                else
                  if b then some ⟨false, false, some 62⟩ else some ⟨false, false, some 63⟩
              else
                if q.val < 65 then
                  if b then some ⟨false, false, some 63⟩ else some ⟨false, false, some 64⟩
                else
                  if q.val < 66 then
                    if b then some ⟨true, true, some 74⟩ else some ⟨false, true, some 66⟩
                  else
                    if b then some ⟨true, true, some 68⟩ else some ⟨false, true, some 67⟩
          else
            if q.val < 72 then
              if q.val < 69 then
                if q.val < 68 then
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 39⟩
                else
                  if b then some ⟨true, true, some 32⟩ else some ⟨false, true, some 69⟩
              else
                if q.val < 70 then
                  if b then some ⟨true, true, some 72⟩ else some ⟨false, true, some 70⟩
                else
                  if q.val < 71 then
                    if b then some ⟨true, true, some 71⟩ else some ⟨false, true, some 31⟩
                  else
                    if b then some ⟨true, true, some 184⟩ else some ⟨false, true, some 40⟩
            else
              if q.val < 74 then
                if q.val < 73 then
                  if b then some ⟨true, true, some 73⟩ else some ⟨false, true, some 41⟩
                else
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 32⟩
              else
                if q.val < 75 then
                  if b then some ⟨true, true, some 85⟩ else some ⟨false, true, some 191⟩
                else
                  if q.val < 76 then
                    if b then some ⟨true, true, some 76⟩ else some ⟨false, true, some 233⟩
                  else
                    if b then some ⟨true, true, some 77⟩ else some ⟨false, true, some 237⟩
    else
      if q.val < 115 then
        if q.val < 96 then
          if q.val < 86 then
            if q.val < 81 then
              if q.val < 79 then
                if q.val < 78 then
                  if b then some ⟨true, true, some 78⟩ else some ⟨false, true, some 254⟩
                else
                  if b then some ⟨true, true, some 79⟩ else some ⟨false, true, some 260⟩
              else
                if q.val < 80 then
                  if b then some ⟨true, true, some 80⟩ else some ⟨false, true, some 261⟩
                else
                  if b then some ⟨true, true, some 81⟩ else some ⟨false, true, some 263⟩
            else
              if q.val < 83 then
                if q.val < 82 then
                  if b then some ⟨true, true, some 82⟩ else some ⟨false, true, some 265⟩
                else
                  if b then some ⟨true, true, some 83⟩ else some ⟨false, true, some 243⟩
              else
                if q.val < 84 then
                  if b then some ⟨true, true, some 84⟩ else some ⟨false, true, some 263⟩
                else
                  if q.val < 85 then
                    if b then some ⟨true, true, some 87⟩ else some ⟨false, true, some 233⟩
                  else
                    if b then some ⟨true, true, some 98⟩ else some ⟨false, true, some 86⟩
          else
            if q.val < 91 then
              if q.val < 88 then
                if q.val < 87 then
                  if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 33⟩
                else
                  if b then some ⟨true, true, some 88⟩ else some ⟨false, true, some 267⟩
              else
                if q.val < 89 then
                  if b then some ⟨true, true, some 89⟩ else some ⟨false, true, some 269⟩
                else
                  if q.val < 90 then
                    if b then some ⟨true, true, some 90⟩ else some ⟨false, true, some 243⟩
                  else
                    if b then some ⟨true, true, some 91⟩ else some ⟨false, true, some 271⟩
            else
              if q.val < 93 then
                if q.val < 92 then
                  if b then some ⟨true, true, some 92⟩ else some ⟨false, true, some 253⟩
                else
                  if b then some ⟨true, true, some 93⟩ else some ⟨false, true, some 225⟩
              else
                if q.val < 94 then
                  if b then some ⟨true, true, some 94⟩ else some ⟨false, true, some 265⟩
                else
                  if q.val < 95 then
                    if b then some ⟨true, true, some 95⟩ else some ⟨false, true, some 280⟩
                  else
                    if b then some ⟨true, true, some 97⟩ else some ⟨false, true, some 96⟩
        else
          if q.val < 105 then
            if q.val < 100 then
              if q.val < 98 then
                if q.val < 97 then
                  if b then some ⟨true, true, some 203⟩ else some ⟨false, true, some 272⟩
                else
                  if b then some ⟨true, true, some 99⟩ else some ⟨false, true, some 271⟩
              else
                if q.val < 99 then
                  if b then some ⟨true, true, some 113⟩ else some ⟨false, true, some 195⟩
                else
                  if b then some ⟨true, true, some 103⟩ else some ⟨false, true, some 100⟩
            else
              if q.val < 102 then
                if q.val < 101 then
                  if b then some ⟨true, true, some 102⟩ else some ⟨false, true, some 101⟩
                else
                  if b then some ⟨true, true, some 186⟩ else some ⟨false, true, some 45⟩
              else
                if q.val < 103 then
                  if b then some ⟨true, true, some 221⟩ else some ⟨false, true, some 282⟩
                else
                  if q.val < 104 then
                    if b then some ⟨true, true, some 105⟩ else some ⟨false, true, some 104⟩
                  else
                    if b then some ⟨true, true, some 233⟩ else some ⟨false, true, some 292⟩
          else
            if q.val < 110 then
              if q.val < 107 then
                if q.val < 106 then
                  if b then some ⟨true, true, some 106⟩ else some ⟨false, true, some 266⟩
                else
                  if b then some ⟨true, true, some 107⟩ else some ⟨false, true, some 232⟩
              else
                if q.val < 108 then
                  if b then some ⟨true, true, some 108⟩ else some ⟨false, true, some 253⟩
                else
                  if q.val < 109 then
                    if b then some ⟨true, true, some 109⟩ else some ⟨false, true, some 237⟩
                  else
                    if b then some ⟨true, true, some 110⟩ else some ⟨false, true, some 293⟩
            else
              if q.val < 112 then
                if q.val < 111 then
                  if b then some ⟨true, true, some 111⟩ else some ⟨false, true, some 260⟩
                else
                  if b then some ⟨true, true, some 112⟩ else some ⟨false, true, some 240⟩
              else
                if q.val < 113 then
                  if b then some ⟨true, true, some 114⟩ else some ⟨false, true, some 258⟩
                else
                  if q.val < 114 then
                    if b then some ⟨true, true, some 124⟩ else some ⟨false, true, some 191⟩
                  else
                    if b then some ⟨true, true, some 115⟩ else some ⟨false, true, some 280⟩
      else
        if q.val < 134 then
          if q.val < 124 then
            if q.val < 119 then
              if q.val < 117 then
                if q.val < 116 then
                  if b then some ⟨true, true, some 116⟩ else some ⟨false, true, some 294⟩
                else
                  if b then some ⟨true, true, some 117⟩ else some ⟨false, true, some 292⟩
              else
                if q.val < 118 then
                  if b then some ⟨true, true, some 118⟩ else some ⟨false, true, some 256⟩
                else
                  if b then some ⟨true, true, some 119⟩ else some ⟨false, true, some 254⟩
            else
              if q.val < 121 then
                if q.val < 120 then
                  if b then some ⟨true, true, some 120⟩ else some ⟨false, true, some 294⟩
                else
                  if b then some ⟨true, true, some 121⟩ else some ⟨false, true, some 295⟩
              else
                if q.val < 122 then
                  if b then some ⟨true, true, some 122⟩ else some ⟨false, true, some 234⟩
                else
                  if q.val < 123 then
                    if b then some ⟨true, true, some 123⟩ else some ⟨false, true, some 258⟩
                  else
                    if b then some ⟨true, true, some 125⟩ else some ⟨false, true, some 296⟩
          else
            if q.val < 129 then
              if q.val < 126 then
                if q.val < 125 then
                  if b then some ⟨true, true, some 144⟩ else some ⟨false, true, some 199⟩
                else
                  if b then some ⟨true, true, some 126⟩ else some ⟨false, true, some 215⟩
              else
                if q.val < 127 then
                  if b then some ⟨true, true, some 131⟩ else some ⟨false, true, some 127⟩
                else
                  if q.val < 128 then
                    if b then some ⟨true, true, some 129⟩ else some ⟨false, true, some 128⟩
                  else
                    if b then some ⟨true, true, some 205⟩ else some ⟨false, true, some 33⟩
            else
              if q.val < 131 then
                if q.val < 130 then
                  if b then some ⟨true, true, some 34⟩ else some ⟨false, true, some 130⟩
                else
                  if b then some ⟨true, true, some 282⟩ else some ⟨false, true, some 195⟩
              else
                if q.val < 132 then
                  if b then some ⟨true, true, some 136⟩ else some ⟨false, true, some 132⟩
                else
                  if q.val < 133 then
                    if b then some ⟨true, true, some 134⟩ else some ⟨false, true, some 133⟩
                  else
                    if b then some ⟨true, true, some 205⟩ else some ⟨false, true, some 37⟩
        else
          if q.val < 144 then
            if q.val < 139 then
              if q.val < 136 then
                if q.val < 135 then
                  if b then some ⟨true, true, some 135⟩ else some ⟨false, true, some 197⟩
                else
                  if b then some ⟨true, true, some 38⟩ else some ⟨false, true, some 282⟩
              else
                if q.val < 137 then
                  if b then some ⟨true, true, some 137⟩ else some ⟨false, true, some 228⟩
                else
                  if q.val < 138 then
                    if b then some ⟨true, true, some 138⟩ else some ⟨false, true, some 207⟩
                  else
                    if b then some ⟨true, true, some 140⟩ else some ⟨false, true, some 139⟩
            else
              if q.val < 141 then
                if q.val < 140 then
                  if b then some ⟨true, true, some 225⟩ else some ⟨false, true, some 297⟩
                else
                  if b then some ⟨true, true, some 141⟩ else some ⟨false, true, some 297⟩
              else
                if q.val < 142 then
                  if b then some ⟨true, true, some 142⟩ else some ⟨false, true, some 296⟩
                else
                  if q.val < 143 then
                    if b then some ⟨true, true, some 143⟩ else some ⟨false, true, some 298⟩
                  else
                    if b then some ⟨true, true, some 145⟩ else some ⟨false, true, some 300⟩
          else
            if q.val < 149 then
              if q.val < 146 then
                if q.val < 145 then
                  if b then some ⟨true, true, some 155⟩ else some ⟨false, true, some 191⟩
                else
                  if b then some ⟨true, true, some 146⟩ else some ⟨false, true, some 302⟩
              else
                if q.val < 147 then
                  if b then some ⟨true, true, some 147⟩ else some ⟨false, true, some 303⟩
                else
                  if q.val < 148 then
                    if b then some ⟨true, true, some 148⟩ else some ⟨false, true, some 234⟩
                  else
                    if b then some ⟨true, true, some 149⟩ else some ⟨false, true, some 266⟩
            else
              if q.val < 151 then
                if q.val < 150 then
                  if b then some ⟨true, true, some 150⟩ else some ⟨false, true, some 239⟩
                else
                  if b then some ⟨true, true, some 151⟩ else some ⟨false, true, some 300⟩
              else
                if q.val < 152 then
                  if b then some ⟨true, true, some 152⟩ else some ⟨false, true, some 293⟩
                else
                  if q.val < 153 then
                    if b then some ⟨true, true, some 153⟩ else some ⟨false, true, some 303⟩
                  else
                    if b then some ⟨true, true, some 154⟩ else some ⟨false, true, some 241⟩
  else
    if q.val < 231 then
      if q.val < 192 then
        if q.val < 173 then
          if q.val < 163 then
            if q.val < 158 then
              if q.val < 156 then
                if q.val < 155 then
                  if b then some ⟨true, true, some 156⟩ else some ⟨false, true, some 305⟩
                else
                  if b then some ⟨true, true, some 168⟩ else some ⟨false, true, some 203⟩
              else
                if q.val < 157 then
                  if b then some ⟨true, true, some 158⟩ else some ⟨false, true, some 157⟩
                else
                  if b then some ⟨true, true, some 239⟩ else some ⟨false, true, some 269⟩
            else
              if q.val < 160 then
                if q.val < 159 then
                  if b then some ⟨true, true, some 159⟩ else some ⟨false, true, some 305⟩
                else
                  if b then some ⟨true, true, some 160⟩ else some ⟨false, true, some 241⟩
              else
                if q.val < 161 then
                  if b then some ⟨true, true, some 161⟩ else some ⟨false, true, some 243⟩
                else
                  if q.val < 162 then
                    if b then some ⟨true, true, some 163⟩ else some ⟨false, true, some 162⟩
                  else
                    if b then some ⟨true, true, some 306⟩ else some ⟨false, true, some 306⟩
          else
            if q.val < 168 then
              if q.val < 165 then
                if q.val < 164 then
                  if b then some ⟨true, true, some 164⟩ else some ⟨false, true, some 295⟩
                else
                  if b then some ⟨true, true, some 165⟩ else some ⟨false, true, some 298⟩
              else
                if q.val < 166 then
                  if b then some ⟨true, true, some 166⟩ else some ⟨false, true, some 307⟩
                else
                  if q.val < 167 then
                    if b then some ⟨true, true, some 167⟩ else some ⟨false, true, some 297⟩
                  else
                    if b then some ⟨true, true, some 169⟩ else some ⟨false, true, some 307⟩
            else
              if q.val < 170 then
                if q.val < 169 then
                  if b then some ⟨true, true, some 178⟩ else some ⟨false, true, some 191⟩
                else
                  if b then some ⟨true, true, some 170⟩ else some ⟨false, true, some 292⟩
              else
                if q.val < 171 then
                  if b then some ⟨true, true, some 172⟩ else some ⟨false, true, some 171⟩
                else
                  if q.val < 172 then
                    if b then some ⟨true, true, some 291⟩ else some ⟨false, true, some 225⟩
                  else
                    if b then some ⟨true, true, some 173⟩ else some ⟨false, true, some 296⟩
        else
          if q.val < 182 then
            if q.val < 177 then
              if q.val < 175 then
                if q.val < 174 then
                  if b then some ⟨true, true, some 174⟩ else some ⟨false, true, some 45⟩
                else
                  if b then some ⟨true, true, none⟩ else some ⟨false, true, some 175⟩
              else
                if q.val < 176 then
                  if b then some ⟨true, true, some 176⟩ else some ⟨false, true, some 45⟩
                else
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 177⟩
            else
              if q.val < 179 then
                if q.val < 178 then
                  if b then some ⟨true, true, some 46⟩ else some ⟨false, true, some 46⟩
                else
                  if b then some ⟨true, true, some 75⟩ else some ⟨false, true, some 179⟩
              else
                if q.val < 180 then
                  if b then some ⟨true, true, some 181⟩ else some ⟨false, true, some 180⟩
                else
                  if q.val < 181 then
                    if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 29⟩
                  else
                    if b then some ⟨true, true, some 215⟩ else some ⟨false, true, some 182⟩
          else
            if q.val < 187 then
              if q.val < 184 then
                if q.val < 183 then
                  if b then some ⟨true, true, some 183⟩ else some ⟨false, true, some 41⟩
                else
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 30⟩
              else
                if q.val < 185 then
                  if b then some ⟨false, false, some 62⟩ else some ⟨false, true, some 42⟩
                else
                  if q.val < 186 then
                    if b then some ⟨false, false, some 62⟩ else some ⟨false, true, some 43⟩
                  else
                    if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 44⟩
            else
              if q.val < 189 then
                if q.val < 188 then
                  if b then some ⟨true, true, some 186⟩ else some ⟨false, true, some 41⟩
                else
                  if b then some ⟨false, false, some 63⟩ else some ⟨false, true, some 187⟩
              else
                if q.val < 190 then
                  if b then some ⟨true, true, some 188⟩ else some ⟨false, true, some 185⟩
                else
                  if q.val < 191 then
                    if b then some ⟨true, true, some 189⟩ else some ⟨false, true, some 42⟩
                  else
                    if b then some ⟨true, true, some 193⟩ else some ⟨false, true, some 192⟩
      else
        if q.val < 211 then
          if q.val < 201 then
            if q.val < 196 then
              if q.val < 194 then
                if q.val < 193 then
                  if b then some ⟨true, true, some 190⟩ else some ⟨false, true, some 39⟩
                else
                  if b then some ⟨true, true, some 194⟩ else some ⟨false, true, some 43⟩
              else
                if q.val < 195 then
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 40⟩
                else
                  if b then some ⟨true, true, some 196⟩ else some ⟨false, true, some 41⟩
            else
              if q.val < 198 then
                if q.val < 197 then
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 34⟩
                else
                  if b then some ⟨true, true, some 198⟩ else some ⟨false, true, some 41⟩
              else
                if q.val < 199 then
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 38⟩
                else
                  if q.val < 200 then
                    if b then some ⟨true, true, some 197⟩ else some ⟨false, true, some 200⟩
                  else
                    if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 37⟩
          else
            if q.val < 206 then
              if q.val < 203 then
                if q.val < 202 then
                  if b then some ⟨true, true, some 202⟩ else some ⟨false, true, some 41⟩
                else
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 36⟩
              else
                if q.val < 204 then
                  if b then some ⟨true, true, some 201⟩ else some ⟨false, true, some 204⟩
                else
                  if q.val < 205 then
                    if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 35⟩
                  else
                    if b then some ⟨true, true, some 184⟩ else some ⟨false, true, some 44⟩
            else
              if q.val < 208 then
                if q.val < 207 then
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 46⟩
                else
                  if b then some ⟨true, true, some 206⟩ else some ⟨false, true, some 41⟩
              else
                if q.val < 209 then
                  if b then some ⟨true, true, some 210⟩ else some ⟨false, true, some 209⟩
                else
                  if q.val < 210 then
                    if b then some ⟨true, true, some 205⟩ else some ⟨false, true, some 45⟩
                  else
                    if b then some ⟨true, true, some 211⟩ else some ⟨false, true, some 41⟩
        else
          if q.val < 221 then
            if q.val < 216 then
              if q.val < 213 then
                if q.val < 212 then
                  if b then some ⟨true, true, some 212⟩ else some ⟨false, true, some 44⟩
                else
                  if b then some ⟨false, false, some 63⟩ else some ⟨false, true, some 207⟩
              else
                if q.val < 214 then
                  if b then some ⟨true, true, some 214⟩ else some ⟨false, true, some 43⟩
                else
                  if q.val < 215 then
                    if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 48⟩
                  else
                    if b then some ⟨true, true, some 218⟩ else some ⟨false, true, some 216⟩
            else
              if q.val < 218 then
                if q.val < 217 then
                  if b then some ⟨true, true, some 217⟩ else some ⟨false, true, some 47⟩
                else
                  if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 42⟩
              else
                if q.val < 219 then
                  if b then some ⟨true, true, some 213⟩ else some ⟨false, true, some 208⟩
                else
                  if q.val < 220 then
                    if b then some ⟨true, true, some 184⟩ else some ⟨false, true, some 46⟩
                  else
                    if b then some ⟨true, true, some 219⟩ else some ⟨false, true, some 33⟩
          else
            if q.val < 226 then
              if q.val < 223 then
                if q.val < 222 then
                  if b then some ⟨true, true, some 195⟩ else some ⟨false, true, some 220⟩
                else
                  if b then some ⟨true, true, some 221⟩ else some ⟨false, true, some 215⟩
              else
                if q.val < 224 then
                  if b then some ⟨true, true, some 219⟩ else some ⟨false, true, some 35⟩
                else
                  if q.val < 225 then
                    if b then some ⟨true, true, some 201⟩ else some ⟨false, true, some 223⟩
                  else
                    if b then some ⟨true, true, some 224⟩ else some ⟨false, true, some 215⟩
            else
              if q.val < 228 then
                if q.val < 227 then
                  if b then some ⟨true, true, some 225⟩ else some ⟨false, true, some 222⟩
                else
                  if b then some ⟨true, true, some 190⟩ else some ⟨false, true, some 47⟩
              else
                if q.val < 229 then
                  if b then some ⟨true, true, some 213⟩ else some ⟨false, true, some 227⟩
                else
                  if q.val < 230 then
                    if b then some ⟨true, true, some 230⟩ else some ⟨false, true, some 208⟩
                  else
                    if b then some ⟨true, true, some 206⟩ else some ⟨false, true, some 43⟩
    else
      if q.val < 269 then
        if q.val < 250 then
          if q.val < 240 then
            if q.val < 235 then
              if q.val < 233 then
                if q.val < 232 then
                  if b then some ⟨true, true, some 229⟩ else some ⟨false, true, some 228⟩
                else
                  if b then some ⟨true, true, some 229⟩ else some ⟨false, true, some 231⟩
              else
                if q.val < 234 then
                  if b then some ⟨true, true, some 232⟩ else some ⟨false, true, some 226⟩
                else
                  if b then some ⟨true, true, some 235⟩ else some ⟨false, true, some 215⟩
            else
              if q.val < 237 then
                if q.val < 236 then
                  if b then some ⟨true, true, some 197⟩ else some ⟨false, true, some 236⟩
                else
                  if b then some ⟨true, true, some 219⟩ else some ⟨false, true, some 37⟩
              else
                if q.val < 238 then
                  if b then some ⟨true, true, some 234⟩ else some ⟨false, true, some 222⟩
                else
                  if q.val < 239 then
                    if b then some ⟨true, true, some 229⟩ else some ⟨false, true, some 42⟩
                  else
                    if b then some ⟨true, true, some 238⟩ else some ⟨false, true, some 231⟩
          else
            if q.val < 245 then
              if q.val < 242 then
                if q.val < 241 then
                  if b then some ⟨true, true, some 234⟩ else some ⟨false, true, some 225⟩
                else
                  if b then some ⟨true, true, some 239⟩ else some ⟨false, true, some 240⟩
              else
                if q.val < 243 then
                  if b then some ⟨true, true, some 238⟩ else some ⟨false, true, some 42⟩
                else
                  if q.val < 244 then
                    if b then some ⟨true, true, some 242⟩ else some ⟨false, true, some 231⟩
                  else
                    if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 29⟩
            else
              if q.val < 247 then
                if q.val < 246 then
                  if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 45⟩
                else
                  if b then some ⟨true, true, some 207⟩ else some ⟨false, true, some 245⟩
              else
                if q.val < 248 then
                  if b then some ⟨true, true, some 246⟩ else some ⟨false, true, some 244⟩
                else
                  if q.val < 249 then
                    if b then some ⟨true, true, some 247⟩ else some ⟨false, true, some 228⟩
                  else
                    if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 41⟩
        else
          if q.val < 259 then
            if q.val < 254 then
              if q.val < 252 then
                if q.val < 251 then
                  if b then some ⟨true, true, some 249⟩ else some ⟨false, true, some 248⟩
                else
                  if b then some ⟨true, true, some 250⟩ else some ⟨false, true, some 243⟩
              else
                if q.val < 253 then
                  if b then some ⟨true, true, some 251⟩ else some ⟨false, true, some 243⟩
                else
                  if b then some ⟨true, true, some 225⟩ else some ⟨false, true, some 252⟩
            else
              if q.val < 256 then
                if q.val < 255 then
                  if b then some ⟨true, true, some 255⟩ else some ⟨false, true, some 239⟩
                else
                  if b then some ⟨true, true, some 253⟩ else some ⟨false, true, some 241⟩
              else
                if q.val < 257 then
                  if b then some ⟨true, true, some 222⟩ else some ⟨false, true, some 225⟩
                else
                  if q.val < 258 then
                    if b then some ⟨true, true, some 242⟩ else some ⟨false, true, some 42⟩
                  else
                    if b then some ⟨true, true, some 259⟩ else some ⟨false, true, some 231⟩
          else
            if q.val < 264 then
              if q.val < 261 then
                if q.val < 260 then
                  if b then some ⟨true, true, some 257⟩ else some ⟨false, true, some 42⟩
                else
                  if b then some ⟨true, true, some 258⟩ else some ⟨false, true, some 256⟩
              else
                if q.val < 262 then
                  if b then some ⟨true, true, some 262⟩ else some ⟨false, true, some 257⟩
                else
                  if q.val < 263 then
                    if b then some ⟨true, true, some 257⟩ else some ⟨false, true, some 258⟩
                  else
                    if b then some ⟨true, true, some 264⟩ else some ⟨false, true, some 222⟩
            else
              if q.val < 266 then
                if q.val < 265 then
                  if b then some ⟨true, true, some 222⟩ else some ⟨false, true, some 251⟩
                else
                  if b then some ⟨true, true, some 222⟩ else some ⟨false, true, some 257⟩
              else
                if q.val < 267 then
                  if b then some ⟨true, true, some 225⟩ else some ⟨false, true, some 234⟩
                else
                  if q.val < 268 then
                    if b then some ⟨true, true, some 266⟩ else some ⟨false, true, some 268⟩
                  else
                    if b then some ⟨true, true, some 250⟩ else some ⟨false, true, some 261⟩
      else
        if q.val < 288 then
          if q.val < 278 then
            if q.val < 273 then
              if q.val < 271 then
                if q.val < 270 then
                  if b then some ⟨true, true, some 256⟩ else some ⟨false, true, some 243⟩
                else
                  if b then some ⟨true, true, some 222⟩ else some ⟨false, true, some 234⟩
              else
                if q.val < 272 then
                  if b then some ⟨true, true, some 243⟩ else some ⟨false, true, some 270⟩
                else
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 273⟩
            else
              if q.val < 275 then
                if q.val < 274 then
                  if b then some ⟨true, true, some 274⟩ else some ⟨false, true, some 29⟩
                else
                  if b then some ⟨true, true, some 278⟩ else some ⟨false, true, some 275⟩
              else
                if q.val < 276 then
                  if b then some ⟨true, true, some 276⟩ else some ⟨false, true, some 29⟩
                else
                  if q.val < 277 then
                    if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 277⟩
                  else
                    if b then some ⟨true, true, some 30⟩ else some ⟨false, true, some 30⟩
          else
            if q.val < 283 then
              if q.val < 280 then
                if q.val < 279 then
                  if b then some ⟨true, true, some 279⟩ else some ⟨false, true, some 30⟩
                else
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 228⟩
              else
                if q.val < 281 then
                  if b then some ⟨true, true, some 281⟩ else some ⟨false, true, some 252⟩
                else
                  if q.val < 282 then
                    if b then some ⟨true, true, some 199⟩ else some ⟨false, true, some 272⟩
                  else
                    if b then some ⟨true, true, some 289⟩ else some ⟨false, true, some 283⟩
            else
              if q.val < 285 then
                if q.val < 284 then
                  if b then some ⟨true, true, some 284⟩ else some ⟨false, true, some 224⟩
                else
                  if b then some ⟨true, true, some 285⟩ else some ⟨false, true, some 43⟩
              else
                if q.val < 286 then
                  if b then some ⟨true, true, some 287⟩ else some ⟨false, true, some 286⟩
                else
                  if q.val < 287 then
                    if b then some ⟨false, false, some 61⟩ else some ⟨false, true, some 45⟩
                  else
                    if b then some ⟨false, false, some 59⟩ else some ⟨false, true, some 288⟩
        else
          if q.val < 298 then
            if q.val < 293 then
              if q.val < 290 then
                if q.val < 289 then
                  if b then some ⟨false, false, some 60⟩ else some ⟨false, true, some 43⟩
                else
                  if b then some ⟨true, true, some 290⟩ else some ⟨false, true, some 45⟩
              else
                if q.val < 291 then
                  if b then some ⟨false, false, some 58⟩ else some ⟨false, true, some 245⟩
                else
                  if q.val < 292 then
                    if b then some ⟨true, true, some 232⟩ else some ⟨false, true, some 237⟩
                  else
                    if b then some ⟨true, true, some 291⟩ else some ⟨false, true, some 250⟩
            else
              if q.val < 295 then
                if q.val < 294 then
                  if b then some ⟨true, true, some 258⟩ else some ⟨false, true, some 243⟩
                else
                  if b then some ⟨true, true, some 258⟩ else some ⟨false, true, some 237⟩
              else
                if q.val < 296 then
                  if b then some ⟨true, true, some 226⟩ else some ⟨false, true, some 258⟩
                else
                  if q.val < 297 then
                    if b then some ⟨true, true, some 251⟩ else some ⟨false, true, some 258⟩
                  else
                    if b then some ⟨true, true, some 239⟩ else some ⟨false, true, some 237⟩
          else
            if q.val < 303 then
              if q.val < 300 then
                if q.val < 299 then
                  if b then some ⟨true, true, some 299⟩ else some ⟨false, true, some 266⟩
                else
                  if b then some ⟨true, true, some 241⟩ else some ⟨false, true, some 234⟩
              else
                if q.val < 301 then
                  if b then some ⟨true, true, some 239⟩ else some ⟨false, true, some 270⟩
                else
                  if q.val < 302 then
                    if b then some ⟨true, true, some 293⟩ else some ⟨false, true, some 257⟩
                  else
                    if b then some ⟨true, true, some 257⟩ else some ⟨false, true, some 301⟩
            else
              if q.val < 305 then
                if q.val < 304 then
                  if b then some ⟨true, true, some 304⟩ else some ⟨false, true, some 241⟩
                else
                  if b then some ⟨true, true, some 267⟩ else some ⟨false, true, some 293⟩
              else
                if q.val < 306 then
                  if b then some ⟨true, true, some 261⟩ else some ⟨false, true, some 237⟩
                else
                  if q.val < 307 then
                    if b then some ⟨true, true, some 257⟩ else some ⟨false, true, some 243⟩
                  else
                    if b then some ⟨true, true, some 302⟩ else some ⟨false, true, some 301⟩

/-- Kernel-check every transition to justify the faster lookup. -/
theorem fastLookup_eq_machine : fastLookup = machine := by
  funext q b
  fin_cases q <;> cases b <;> decide +kernel

/-- Blank tape, head at zero, original initial label `0.boot.A`. -/
def initial : Configuration 308 := ⟨some 0, 0, fun _ => false⟩

/-- The intended binary-tape halting proposition. -/
def Halts : Prop := Machine.halts machine initial

/-- The state type has exactly 308 working states; halting is separate. -/
theorem state_count : Fintype.card (Fin 308) = 308 := by simp

end TinyZF.Machine308
