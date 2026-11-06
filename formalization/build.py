"""Build project modules with the existing pinned compatible local runtime.

No files in the reused runtime or the other project are modified.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding='utf-8')
sys.stderr.reconfigure(encoding='utf-8')

ROOT = Path(__file__).resolve().parent
RUNTIME = Path('C:/Users/Administrator/Documents/ChatGPT/jsp423_fast_runtime_20261101')
LEAN = ROOT.parent/'jsp423-repro/_toolchain/bin/lean.exe'
LIBRARIES = RUNTIME/'libraries'
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(ROOT), str(ROOT/'vendor/aintlib/olean'), *[str(p) for p in LIBRARIES.iterdir() if p.is_dir()]])
env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
env['LEAN_NUM_THREADS'] = '1'
version = subprocess.run([str(LEAN),'--version'],env=env,text=True,capture_output=True,check=True).stdout.strip()
if 'version 4.33.0,' not in version:
    raise RuntimeError('Unexpected Lean version: '+version)
modules = sys.argv[1:] or ['Carlet/Elementary.lean', 'Carlet/Statement.lean', 'Carlet/K4PoleData.lean', 'Carlet/K4PoleNumerator.lean',
    'Carlet/K4PoleRoots.lean',
    'Carlet/SubspacePolynomial.lean', 'Carlet/CompositionCoefficients.lean',
    'Carlet/ImagePolynomial.lean', 'Carlet/QuadraticReconstruction.lean',
    'Carlet/IndexedProduct.lean', 'Carlet/QuadraticRows.lean',
    'Carlet/ReciprocalBlocks.lean', 'Carlet/ReverseCarlet.lean', 'Carlet/BaseChange.lean',
    'Carlet/QuadraticPointMap.lean', 'Carlet/ForwardScales.lean',
    'Carlet/ForwardCoordinates.lean', 'Carlet/CoordinateRoundTrip.lean',
    'Carlet/CoordinateCongruence.lean', 'Carlet/FiniteCoordinates.lean',
    'Carlet/FiniteNaturality.lean', 'Carlet/PointFunctors.lean',
    'Carlet/QuadraticPolynomial.lean', 'Carlet/QuadraticRelations.lean',
    'Carlet/QuadraticRepresentation.lean', 'Carlet/OpenInverseCoordinates.lean',
    'Carlet/OpenPolynomial.lean', 'Carlet/OpenRepresentation.lean',
    'Carlet/PresentationRingIso.lean', 'Carlet/PresentationSchemeIso.lean',
    'Carlet/TransferOperator.lean', 'Carlet/ImageBijection.lean',
    'Carlet/TraceDuality.lean', 'Carlet/ArtinSchreier.lean',
    'Carlet/ArtinSchreierPolynomial.lean', 'Carlet/SubspaceSupport.lean',
    'Carlet/FrobeniusCoefficients.lean', 'Carlet/NextCoefficient.lean',
    'Carlet/DualPolynomial.lean', 'Carlet/DualCoefficients.lean',
    'Carlet/DualSubspacePolynomial.lean', 'Carlet/SubspaceScaling.lean',
    'Carlet/CoefficientScaling.lean', 'Carlet/IncidenceCounting.lean',
    'Carlet/DistributionRecursion.lean', 'Carlet/ProbabilityNormalization.lean',
    'Carlet/SubspaceCount.lean', 'Carlet/AdjacentCountRatio.lean',
    'Carlet/ConcreteProbabilityRecursion.lean', 'Carlet/TransferContraction.lean',
    'Carlet/TransferEnergy.lean', 'Carlet/TwoStepEnergy.lean',
    'Carlet/ProbabilityEnergy.lean', 'Carlet/SmallProbability.lean', 'Carlet/AdditiveClosure.lean',
    'Carlet/LowDimensionReduction.lean', 'Carlet/KloostermanThree.lean',
    'Carlet/TwoBaseReduction.lean', 'Carlet/SubfieldFive.lean',
    'Carlet/RemainingCases.lean', 'Carlet/Frobenius21.lean',
    'Carlet/FivePolynomialRoots.lean', 'Carlet/SmallFrobenius.lean',
    'Carlet/FiveDimension21.lean', 'Carlet/FieldTransport.lean',
    'Carlet/FiveDimension31.lean', 'Carlet/FourDimension7.lean',
    'Carlet/FourDimension15.lean',
    'Carlet/Frobenius11Scratch.lean', 'Carlet/N11FieldBridgeProbe.lean',
    'Carlet/N11AllInverseProbe.lean', 'Carlet/N11UniquenessProbe.lean',
    'Carlet/N11DistinctProbe.lean', 'Carlet/N11ComboProbe.lean',
    'Carlet/N11SubsetSumProbe.lean', 'Carlet/N11SubsetNonzeroProbe.lean',
    'Carlet/N11SupportLinearProbe.lean', 'Carlet/N11CodeEquivProbe.lean',
    'Carlet/N11DecodeInv01Fast.lean', 'Carlet/N11DecodeInv02to08.lean',
    'Carlet/N11DecodeInv09to16.lean', 'Carlet/N11DecodeInv17to24.lean',
    'Carlet/N11DecodeInv25to31.lean', 'Carlet/N11DecodeInverseAudit.lean',
    'Carlet/N11InvForTerm.lean', 'Carlet/N11K5CompleteProbe.lean',
    'Carlet/N11K5SubfieldProbe.lean', 'Carlet/RemainingCases11.lean',
    'Carlet/Frobenius13Probe.lean', 'Carlet/N13InverseProbe.lean',
    'Carlet/N13ComboProbe.lean', 'Carlet/N13SubsetSumProbe.lean',
    'Carlet/N13SubsetNonzeroProbe.lean', 'Carlet/N13FieldBridgeProbe.lean',
    'Carlet/N13SupportLinearProbe.lean', 'Carlet/N13CodeEquivProbe.lean',
    'Carlet/N13DecodeInverseProbe.lean', 'Carlet/N13InvForTerm.lean',
    'Carlet/N13K5CompleteProbe.lean', 'Carlet/N13K5SubfieldProbe.lean',
    'Carlet/N13K4GeneratedData.lean', 'Carlet/N13K4SubsetSums.lean',
    'Carlet/N13K4CodeEquivProbe.lean', 'Carlet/N13K4CompleteProbe.lean',
    'Carlet/N13K4InverseSumProbe.lean', 'Carlet/N13K4FourCertificate.lean',
    'Carlet/RemainingCases13.lean', 'Carlet/Frobenius17Probe.lean',
    'Carlet/N17N19InverseProbe.lean',
    'Carlet/N17InverseAdjoinProbe.lean', 'Carlet/N17FieldBridgeProbe.lean',
    'Carlet/N17ComboProbe.lean', 'Carlet/N17SubsetSumProbe.lean',
    'Carlet/N17SubsetNonzeroProbe.lean', 'Carlet/N17SupportLinearProbe.lean',
    'Carlet/N17CodeEquivProbe.lean', 'Carlet/N17DecodeInverseProbe.lean',
    'Carlet/N17InvForTerm.lean', 'Carlet/N17K5CompleteProbe.lean',
    'Carlet/RemainingCases17.lean',
    'Carlet/N17FourInverseProbe.lean', 'Carlet/N17FourInverseAdjoinProbe.lean',
    'Carlet/N17FourComboProbe.lean', 'Carlet/N17FourSubsetSumProbe.lean',
    'Carlet/N17FourSubsetNonzeroProbe.lean', 'Carlet/N17FourSupportLinearProbe.lean',
    'Carlet/N17FourCodeEquivProbe.lean', 'Carlet/N17FourDecodeInverseProbe.lean',
    'Carlet/N17FourInvForTerm.lean', 'Carlet/N17FourK4CompleteProbe.lean',
    'Carlet/RemainingCases17Four.lean',
    'Carlet/Frobenius9Probe.lean', 'Carlet/N9InverseProbe.lean',
    'Carlet/N9InverseAdjoinProbe.lean', 'Carlet/N9FieldBridgeProbe.lean',
    'Carlet/N9ComboProbe.lean', 'Carlet/N9SubsetSumProbe.lean',
    'Carlet/N9SubsetNonzeroProbe.lean', 'Carlet/N9SupportLinearProbe.lean',
    'Carlet/N9CodeEquivProbe.lean', 'Carlet/N9DecodeInverseProbe.lean',
    'Carlet/N9InvForTerm.lean', 'Carlet/N9K4CompleteProbe.lean',
    'Carlet/RemainingCases9.lean', 'Carlet/N9BoundaryProbe.lean',
    'Carlet/N11FourInverseProbe.lean', 'Carlet/N11FourInverseAdjoinProbe.lean',
    'Carlet/N11FourComboProbe.lean', 'Carlet/N11FourSubsetSumProbe.lean',
    'Carlet/N11FourSubsetNonzeroProbe.lean', 'Carlet/N11FourSupportLinearProbe.lean',
    'Carlet/N11FourCodeEquivProbe.lean', 'Carlet/N11FourDecodeInverseProbe.lean',
    'Carlet/N11FourInvForTerm.lean', 'Carlet/N11FourK4CompleteProbe.lean',
    'Carlet/RemainingCases11Four.lean', 'Carlet/N11BoundaryProbe.lean',
    'Carlet/F19NamedBase.lean', 'Carlet/F19NamedMiddle.lean',
    'Carlet/F19NamedTail.lean', 'Carlet/F19NamedStage1.lean',
    'Carlet/F19NamedIter.lean', 'Carlet/F19NamedIterBridge.lean',
    'Carlet/F19NamedIrreducible.lean', 'Carlet/N19ModulusBridgeProbe.lean',
    'Carlet/N19InverseAdjoinProbe.lean', 'Carlet/N19FieldBridgeProbe.lean',
    'Carlet/N19ComboProbe.lean', 'Carlet/N19SubsetSumProbe.lean',
    'Carlet/N19SubsetNonzeroProbe.lean', 'Carlet/N19SupportLinearProbe.lean',
    'Carlet/N19CodeEquivProbe.lean', 'Carlet/N19DecodeInverseProbe.lean',
    'Carlet/N19InvForTerm.lean', 'Carlet/N19K5CompleteProbe.lean',
    'Carlet/RemainingCases19.lean',
    'Carlet/N19FourInverseProbe.lean', 'Carlet/N19FourInverseAdjoinProbe.lean',
    'Carlet/N19FourComboProbe.lean', 'Carlet/N19FourSubsetSumProbe.lean',
    'Carlet/N19FourSubsetNonzeroProbe.lean', 'Carlet/N19FourSupportLinearProbe.lean',
    'Carlet/N19FourCodeEquivProbe.lean', 'Carlet/N19FourDecodeInverseProbe.lean',
    'Carlet/N19FourInvForTerm.lean', 'Carlet/N19FourK4CompleteProbe.lean',
    'Carlet/RemainingCases19Four.lean',
    'Carlet/N9K5InverseProbe.lean', 'Carlet/N9K5InverseAdjoinProbe.lean',
    'Carlet/N9K5ComboProbe.lean', 'Carlet/N9K5CodeEquivProbe.lean',
    'Carlet/N9K5SubsetSumProbe.lean', 'Carlet/N9K5SubsetNonzeroProbe.lean',
    'Carlet/N9K5SupportLinearProbe.lean', 'Carlet/N9K5DecodeInverseProbe.lean',
    'Carlet/N9K5InvForTermProbe.lean', 'Carlet/N9K5CompleteProbe.lean',
    'Carlet/N9K5SubfieldProbe.lean', 'Carlet/RemainingCases9K5Probe.lean',
    'Carlet/Frobenius23Base.lean',
    'Carlet/Frobenius23Rel1.lean', 'Carlet/Frobenius23Rel2.lean',
    'Carlet/Frobenius23Rel3.lean', 'Carlet/Frobenius23Rel4.lean',
    'Carlet/Frobenius23Chain1.lean', 'Carlet/Frobenius23Chain2.lean',
    'Carlet/Frobenius23Chain3.lean', 'Carlet/Frobenius23Chain4.lean',
    'Carlet/Frobenius23Chain5.lean', 'Carlet/Frobenius23Chain6.lean',
    'Carlet/Frobenius23Chain7.lean', 'Carlet/Frobenius23Chain8.lean',
    'Carlet/Frobenius23Chain9.lean', 'Carlet/Frobenius23Chain10.lean',
    'Carlet/Frobenius23Chain11.lean', 'Carlet/Frobenius23Chain12.lean',
    'Carlet/Frobenius23Frob.lean', 'Carlet/Frobenius23DegreeCriterionProbe.lean',
    'Carlet/Frobenius23Probe.lean', 'Carlet/N23K5InverseProbe.lean',
    'Carlet/N23K5InverseAdjoinProbe.lean', 'Carlet/N23FieldBridgeProbe.lean',
    'Carlet/N23K5ComboProbe.lean', 'Carlet/N23K5CodeEquivProbe.lean',
    'Carlet/N23K5SubsetSumProbe.lean', 'Carlet/N23K5SubsetNonzeroProbe.lean',
    'Carlet/N23K5DecodeInverseProbe.lean', 'Carlet/N23K5InvForTermProbe.lean',
    'Carlet/N23K5SupportLinearProbe.lean', 'Carlet/N23K5CompleteProbe.lean',
    'Carlet/RemainingCases23K5Probe.lean',
    'Carlet/K4ASFactorCharTwoProbe.lean',
    'Carlet/K4ASFactorizationBridgeProbe.lean',
    'Carlet/K4ArtinSchreierWeierstrassProbe.lean',
    'Carlet/K4ASWeierstrassCurveProbe.lean',
    'Carlet/K4ASWeierstrassInverseProbe.lean',
    'Carlet/K4ASWeierstrassReverseNumeratorProbe.lean',
    'Carlet/K4ASWeierstrassExceptionalCountProbe.lean',
    'Carlet/K4ASWeierstrassGenericInjectionProbe.lean',
    'Carlet/K4ASWeierstrassSourceCountProbe.lean',
    'Carlet/K4ASWeierstrassFiberTraceProbe.lean',
    'Carlet/K4NormOneCountArithmeticProbe.lean',
    'Carlet/K4NormOneParametrizationProbe.lean',
    'Carlet/K4GeneralTraceCountProbe.lean',
    'Carlet/K4ThetaProbe.lean',
    'Carlet/K4BadLocusSZProbe.lean',
    'Carlet/K4TracePlaneCardProbe.lean',
    'Carlet/K4CoeffRecursionProbe.lean',
    'Carlet/K4CoeffEightProbe.lean',
    'Carlet/K4ThetaIdentityProbe.lean',
    'Carlet/K4ThetaSpecializationProbe.lean',
    'Carlet/K4ThetaCoefficientBridgeProbe.lean',
    'Carlet/K4ThetaSpanBridgeProbe.lean',
    'Carlet/K4ThetaAsThreeSpaceImageProbe.lean',
    'Carlet/K4ArtinSchreierFactorProbe.lean',
    'Carlet/K4TraceShiftProbe.lean',
    'Carlet/K4ParametricExtensionProbe.lean',
    'Carlet/K4NormOneThetaBridgeProbe.lean',
    'Carlet/K4SmallOddRangeProbe.lean',
    'Carlet/K4AllOddDegreesProbe.lean',
    'Carlet/Frobenius29Base.lean', 'Carlet/Frobenius29Rel1.lean',
    'Carlet/Frobenius29Rel2.lean', 'Carlet/Frobenius29Rel3.lean',
    'Carlet/Frobenius29Rel4.lean', 'Carlet/Frobenius29Rel5.lean',
    'Carlet/Frobenius29Rel6.lean', 'Carlet/Frobenius29Probe.lean',
    'Carlet/Frobenius29K5Probe.lean',
    'Carlet/N29K5InverseProbe.lean',
    'Carlet/N29K5InverseAdjoinProbe.lean', 'Carlet/N29K5ComboProbe.lean',
    'Carlet/N29K5CodeEquivProbe.lean', 'Carlet/N29K5SubsetSumProbe.lean',
    'Carlet/N29K5SubsetNonzeroProbe.lean', 'Carlet/N29FieldBridgeProbe.lean',
    'Carlet/N29K5FieldBridgeProbe.lean',
    'Carlet/N29K5DecodeInversePart1.lean', 'Carlet/N29K5DecodeInversePart2.lean',
    'Carlet/N29K5DecodeInversePart3.lean', 'Carlet/N29K5DecodeInversePart4.lean',
    'Carlet/N29K5DecodeInverse21Probe.lean', 'Carlet/N29K5DecodeInverse22Probe.lean',
    'Carlet/N29K5DecodeInverse23Probe.lean', 'Carlet/N29K5DecodeInverse24Probe.lean',
    'Carlet/N29K5DecodeInverse25Probe.lean', 'Carlet/N29K5DecodeInverse26Probe.lean',
    'Carlet/N29K5DecodeInverse27Probe.lean', 'Carlet/N29K5DecodeInverse28Probe.lean',
    'Carlet/N29K5DecodeInverse29Probe.lean', 'Carlet/N29K5DecodeInverse30Probe.lean',
    'Carlet/N29K5DecodeInverse31Probe.lean', 'Carlet/N29K5DecodeInverseProbe.lean',
    'Carlet/N29K5InvForTermProbe.lean', 'Carlet/N29K5SupportLinearProbe.lean',
    'Carlet/N29K5CompleteProbe.lean', 'Carlet/RemainingCases29K5Probe.lean',
    'Carlet/MainTheoremAssembly.lean',
    'Carlet/RemainingCasesK5Below37.lean',
    'Carlet/LowDimensionalK5Assembly.lean',
    'Carlet/Theta5CoefficientBridgeProbe.lean',
    'Carlet/K5NormOneTraceCountProbe.lean',
    'Carlet/K5RankThreeSeedProbe.lean',
    'Carlet/K5NormOneTracePlaneProbe.lean',
    'Carlet/K5NormOneConstructionProbe.lean',
    'Carlet/MainTheorem.lean']
logs=[]
for module in modules:
    path=(ROOT/module).resolve()
    if not path.is_relative_to(ROOT) or not path.exists(): raise ValueError(module)
    target=path.with_suffix('.olean')
    run=subprocess.run([str(LEAN),'-j1','-o',str(target),str(path)],cwd=ROOT,env=env,text=True,capture_output=True,encoding='utf-8',errors='replace')
    print(run.stdout, end=''); print(run.stderr, end='',file=sys.stderr)
    combined=run.stdout+run.stderr
    hole_free=('sorryAx' not in combined and 'declaration uses `sorry`' not in combined)
    theorem_axioms={name:([s.strip() for s in names.split(',')] if names.strip() else [])
        for name,names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",combined)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",combined):
        theorem_axioms[name]=[]
    axiom_audit=all(set(names)<={'propext','Classical.choice','Quot.sound'} for names in theorem_axioms.values())
    logs.append(dict(module=module,exit_code=run.returncode,hole_free_output=hole_free,
        printed_axiom_audit=axiom_audit,theorem_axioms=theorem_axioms,
        source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        olean_sha256=hashlib.sha256(target.read_bytes()).hexdigest() if run.returncode==0 and target.exists() else None,
        stdout=run.stdout,stderr=run.stderr))
    if run.returncode or not hole_free or not axiom_audit: break
receipt={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':version,'lean_executable':str(LEAN),'mathlib_source_commit':'db584cd6d46c92f209a44c0f1c829460d327499d','lean_path':env['LEAN_PATH'],'modules':logs}
(ROOT/'build_receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2),encoding='utf-8')
sys.exit(any(item['exit_code'] or not item['hole_free_output'] or not item['printed_axiom_audit'] for item in logs))


