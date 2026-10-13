import TinyZF.Tape.Cycles

set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-! # Certified bootstrap of the literal 308-state machine

Generated checkpoints bound kernel reduction depth. The checkpoint producer
is untrusted: `checkTrace_sound` and `boot_checked` verify every literal step.
No execution log, native evaluation axiom, or external prover is trusted. -/
namespace TinyZF.Tape.Bootstrap

/-- A specialized lookup for the five frequently used bootstrap states.
 The fallback is the literal table, and equality is proved immediately below. -/
private def fast : Machine 308 := fun q b =>
  match q.val, b with
  | 0, false => some ⟨true, true, some 1⟩
  | 0, true => some ⟨false, false, some 2⟩
  | 1, false => some ⟨false, true, some 2⟩
  | 1, true => some ⟨false, true, some 1⟩
  | 2, false => some ⟨true, false, some 3⟩
  | 2, true => some ⟨false, true, some 4⟩
  | 3, false => some ⟨false, false, some 4⟩
  | 3, true => some ⟨false, false, some 64⟩
  | 4, false => some ⟨true, false, some 0⟩
  | 4, true => some ⟨false, false, some 1⟩
  | _, _ => Machine308.machine q b

/-- Specializing the bootstrap lookup does not change any transition. -/
private theorem fast_eq : fast = Machine308.machine := by
  funext q b
  rcases q with ⟨q, hq⟩
  cases b <;> unfold fast <;> split <;>
    simp_all only [Bool.false_eq_true, Bool.true_eq_false] <;> rfl

/-- Least-significant bits of a fixed-width binary numeral. -/
private def revBits : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, v => (v % 2 == 1) :: revBits k (v/2)

/-- Finite tape prefix, preserving the specified number of leading zeros. -/
private def bits (width value : Nat) : List Bool := (revBits width value).reverse

/-- Initial finite description of the completely blank tape. -/
def initial : Snapshot 308 := ⟨some 0, [], []⟩

/-- Forty proposed segments covering the 39,769-step bootstrap. -/
def checkpoints : List (Nat × Snapshot 308) := [
  (1000, ⟨some 1, bits 57 19215930786089097, bits 14 5461⟩),
  (1000, ⟨some 1, bits 71 1259297728765247391881, bits 29 447436117⟩),
  (1000, ⟨some 2, bits 115 5538449982437187593703615088855177, bits 9 85⟩),
  (1000, ⟨some 2, bits 111 173076561951160995410530386086025, bits 25 22369621⟩),
  (1000, ⟨some 1, bits 144 19698991592035383775023217730644619014211721, bits 15 21845⟩),
  (1000, ⟨some 1, bits 166 24942961285099369347754243754298495449373906339977, bits 11 1365⟩),
  (1000, ⟨some 1, bits 182 817330955128474073387393565023177806707628715832543369, bits 10 341⟩),
  (1000, ⟨some 0, bits 98 21127510003843455034990299273, bits 109 540864462420717758868639184147797⟩),
  (1000, ⟨some 4, bits 144 743358173641324513742126697434175158913161, bits 72 1574122160956548404565⟩),
  (1000, ⟨some 4, bits 150 761198769443238098299256561946246264144824457, bits 75 6296488643826193618261⟩),
  (1000, ⟨some 0, bits 154 1522397538886357903670001826278904248131946633, bits 80 1007438183012190978921813⟩),
  (1000, ⟨some 1, bits 148 190299692360794655759531619735068592774350985, bits 92 4126466797617934249663747413⟩),
  (1000, ⟨some 2, bits 188 52309181128222339698631578528092287510733828481249478793, bits 61 384307168202282325⟩),
  (1000, ⟨some 4, bits 148 190299692360794651034727136462397830670616713, bits 107 27043212804868893898596335048021⟩),
  (1000, ⟨some 0, bits 96 5284537137754253452508694665, bits 165 19486688497745372242715797769550440262079100573013⟩),
  (1000, ⟨some 1, bits 72 629648941788254734473, bits 195 16755284580133718184717927496843380407564881069207383790933⟩),
  (1000, ⟨some 3, bits 74 629648941788254734473, bits 199 334778759220622974071242102571075542192125623704748507354453⟩),
  (1000, ⟨some 4, bits 116 44307599859502390366668797587785865, bits 163 1948668849774537224271579776955044026207910057301⟩),
  (1000, ⟨some 2, bits 276 16188907435214408924328849223529324222020056992101162677098437613591434296887380105, bits 9 85⟩),
  (1000, ⟨some 1, bits 208 219400607642827472287329224340980067331031467812822918688704649, bits 80 1007438183012190978921813⟩),
  (1000, ⟨some 1, bits 94 10563755007589701162608658569, bits 200 1339115036882491896284968410284302168768502494818994029417813⟩),
  (1000, ⟨some 1, bits 282 2072180151707444342314092700611753500418567294988948822668599903723188868659924207753, bits 15 21845⟩),
  (1000, ⟨some 2, bits 122 354460798875977566144924540606122121, bits 181 2043327387821185144477796036200412244824985496244802901⟩),
  (1000, ⟨some 2, bits 228 57514552889921364895289632185641878770425908101419907788427007395977, bits 81 402975273204876391568725⟩),
  (1000, ⟨some 4, bits 132 181483929024500513847136427153100933257, bits 180 510831846955296286119449009050103061206246374061200725⟩),
  (1000, ⟨some 0, bits 266 7904739958600785607582445909926427842783230953174395838426971068414823569590409, bits 52 3752999689475413⟩),
  (1000, ⟨some 1, bits 90 330117343809473992546879625, bits 231 2300582115596854595811585287425675150817036324056795518387508074599765⟩),
  (1000, ⟨some 4, bits 284 1036090075853722171157046350305876750209283647494474411334299951860748974356238469257, bits 40 366503875925⟩),
  (1000, ⟨some 0, bits 142 371679086642177052358928637884207209154697, bits 188 326932382051389623116447365792065959171997679399168464213⟩),
  (1000, ⟨some 1, bits 128 90741964512250256923566561983961008265, bits 205 34281344944191792544895191303278135520473663867366247153096021⟩),
  (1000, ⟨some 1, bits 172 798174760867650447061639076640786033134761077672073, bits 175 15963495217353008941232781532815720662695199189456213⟩),
  (1000, ⟨some 1, bits 30 80251017, bits 332 1458167149855341282915001484745080910235446287262141624283847070939968666132917282149009517689787733⟩),
  (1000, ⟨some 0, bits 350 152899907737260468754874389941951350499952979732435489579756543811227955610204537396774748472365602605193, bits 24 13981013⟩),
  (1000, ⟨some 0, bits 344 2389061059087830265842326808463932971137863050586417503435091905266894196643096707090743481438380263561, bits 33 3579139413⟩),
  (1000, ⟨some 0, bits 312 561271312679362066303165735346397329308381258068087634925277898478777194128124707110738495625, bits 80 1007438183012190978921813⟩),
  (1000, ⟨some 1, bits 304 8755010873287593324941257198309473221352456866943388510546578639621017961274507551887100041, bits 91 1650586719047173699865498965⟩),
  (1000, ⟨some 4, bits 400 1377199934979684581149823558401616146821041575965324406386048420752923380743691038130768346905217535113222739044178888841, bits 7 21⟩),
  (1000, ⟨some 0, bits 386 10507201652371861123274410696289260001625345439435694967247560503054868557077029438694526332409179886688629934295177, bits 24 13981013⟩),
  (1000, ⟨some 2, bits 390 336230452875899555944781142187926362109183614606286660762718864315653732143810181539642437273429351516969503853938825, bits 29 89478485⟩),
  (769, ⟨some 65, bits 9 256, bits 421 6885999674898422905749117792008031664879215447544596034215091617441726992044909910420578229920531981578341460282434737493⟩)
]

/-- A checked segment followed by a checked tail certifies their concatenation. -/
private theorem checked_cons {m : Machine 308} {s t : Snapshot 308} {k : Nat}
    {rest : List (Nat × Snapshot 308)}
    (h : Snapshot.run m k s = t) (hr : checkTrace m t rest = true) :
    checkTrace m s ((k,t)::rest) = true := by
  simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h, hr⟩

/-- Kernel reduction checks every proposed segment against the literal table. -/
theorem boot_checked : checkTrace Machine308.machine initial checkpoints = true := by
  rw [← fast_eq]
  unfold checkpoints
  repeat first | refine checked_cons (by decide +kernel) ?_ | rfl

/-- Boot leaves a fixed unused prefix followed by zero-valued registers. -/
def bootRegisters : List Nat := List.replicate 132 0 ++ 1 :: List.replicate 68 0

/-- The initial machine reaches the interpreter entry with an 18-cell gap.
This is a proof of actual tape execution, not a bounded-run assumption. -/
theorem bootstrap : Exec Machine308.machine (ofConfiguration Machine308.initial)
    (zc 65 [true] (zeros 18 ++ sepsR bootRegisters)) := by
  have h := checkTrace_sound Machine308.machine initial checkpoints boot_checked
  have hv : (traceEnd initial checkpoints).view =
      zc 65 ([true] ++ zeros 8) (zeros 18 ++ sepsR bootRegisters) := by rfl
  rw [hv, zc_padl] at h
  exact h

/-- The checked bootstrap establishes exactly the zero-register boundary
 used by the unbounded primitive-program simulation. -/
theorem boundary : Exec Framework.m (ofConfiguration Machine308.initial)
    (Framework.boundary [] 0 18 (fun _ => 0)) := by
  rw [Framework.boundary_zero]
  have hr : Framework.junk ++ Framework.registers (fun _ => 0) 0 10 =
      bootRegisters := by decide +kernel
  simpa only [List.nil_append, hr] using bootstrap

end TinyZF.Tape.Bootstrap
