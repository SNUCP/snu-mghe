package mkckks

import (
	"flag"
	"fmt"
	"strconv"
	"testing"

	"mk-lattigo/mkrlwe"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"

	"github.com/stretchr/testify/require"
	"math"
	"math/big"
	"math/cmplx"
)

// Returns the ceil(log2) of the sum of the absolute value of all the coefficients
func log2OfInnerSum(level int, ringQ *ring.Ring, poly *ring.Poly) (logSum float64) {
	sumRNS := make([]uint64, level+1)

	for j := 0; j < ringQ.N; j++ {

		for i := 0; i < level+1; i++ {
			coeffs := poly.Coeffs[i]
			sumRNS[i] = coeffs[j]
		}

		var qi uint64
		var crtReconstruction *big.Int

		sumBigInt := ring.NewUint(0)
		QiB := new(big.Int)
		tmp := new(big.Int)
		modulusBigint := ring.NewInt(1)

		for i := 0; i < level+1; i++ {

			qi = ringQ.Modulus[i]
			QiB.SetUint64(qi)

			modulusBigint.Mul(modulusBigint, QiB)

			crtReconstruction = new(big.Int)
			crtReconstruction.Quo(ringQ.ModulusBigint, QiB)
			tmp.ModInverse(crtReconstruction, QiB)
			tmp.Mod(tmp, QiB)
			crtReconstruction.Mul(crtReconstruction, tmp)

			sumBigInt.Add(sumBigInt, tmp.Mul(ring.NewUint(sumRNS[i]), crtReconstruction))
		}

		sumBigInt.Mod(sumBigInt, modulusBigint)
		sumBigInt.Abs(sumBigInt)
		logSum1 := sumBigInt.BitLen()

		sumBigInt.Sub(sumBigInt, modulusBigint)
		sumBigInt.Abs(sumBigInt)
		logSum2 := sumBigInt.BitLen()

		if logSum1 < logSum2 {
			logSum += float64(logSum1) / float64(ringQ.N)
		} else {
			logSum += float64(logSum2) / float64(ringQ.N)
		}
	}

	return
}

var maxUsers = flag.Int("n", 8, "maximum number of parties")

func GetTestName(params Parameters, opname string) string {
	return fmt.Sprintf("%slogN=%d/LogSlots=%d/logQP=%d/levels=%d/",
		opname,
		params.LogN(),
		params.LogSlots(),
		params.LogQP(),
		params.MaxLevel()+1)
}

type testParams struct {
	params Parameters
	ringQ  *ring.Ring
	ringP  *ring.Ring
	prng   utils.PRNG
	kgen   *mkrlwe.KeyGenerator
	skSet  *mkrlwe.SecretKeySet
	pkSet  *mkrlwe.PublicKeySet
	rlkSet *mkrlwe.RelinearizationKeySet
	rtkSet *mkrlwe.RotationKeySet
	cjkSet *mkrlwe.ConjugationKeySet

	encryptor *Encryptor
	decryptor *Decryptor
	evaluator *Evaluator
	idset     *mkrlwe.IDSet
}

var (
	PN15QP880 = ckks.ParametersLiteral{
		LogN:     15,
		LogSlots: 14,
		//55 + 13x54
		Q: []uint64{
			0x7fffffffba0001,
			0x3fffffffd60001, 0x3fffffffca0001,
			0x3fffffff6d0001, 0x3fffffff5d0001,
			0x3fffffff550001, 0x3fffffff390001,
			0x3fffffff360001, 0x3fffffff2a0001,
			0x3fffffff000001, 0x3ffffffefa0001,
			0x3ffffffef40001, 0x3ffffffed70001,
			0x3ffffffed30001,
		},
		P: []uint64{

			// 30, 45, 60 x 2

			0x3ffc0001, 0x3fde0001,

			//0x1fffffc20001, 0x1fffff980001,

			//0xffffffffffc0001, 0xfffffffff840001,
		},
		Scale: 1 << 54,
		Sigma: rlwe.DefaultSigma,
	}

	PN14QP439 = ckks.ParametersLiteral{
		LogN:     14,
		LogSlots: 13,
		Q: []uint64{
			// 53 + 5x52
			0x1fffffffd80001,
			0xffffffff00001, 0xfffffffe40001,
			0xfffffffe20001, 0xfffffffbe0001,
			0xfffffffa60001,
		},
		P: []uint64{
			// 30, 45, 60 x 2

			//0x3ffc0001, 0x3fde0001,

			//0x1fffffc20001, 0x1fffff980001,

			0xffffffffffc0001, 0xfffffffff840001,
		},
		Scale: 1 << 52,
		Sigma: rlwe.DefaultSigma,
	}
)

func TestCKKS(t *testing.T) {

	//defaultParams := []ckks.ParametersLiteral{PN15QP880}
	defaultParams := []ckks.ParametersLiteral{PN14QP439}

	for _, defaultParam := range defaultParams {
		ckksParams, err := ckks.NewParametersFromLiteral(defaultParam)

		if err != nil {
			panic(err)
		}

		if ckksParams.PCount() < 2 {
			continue
		}

		params := NewParameters(ckksParams)
		userList := make([]string, *maxUsers)
		idset := mkrlwe.NewIDSet()

		for i := range userList {
			userList[i] = "user" + strconv.Itoa(i)
			idset.Add(userList[i])
		}

		var testContext *testParams
		if testContext, err = genTestParams(params, idset); err != nil {
			panic(err)
		}

		testEncAndDec(testContext, userList, t)

		for numUsers := 2; numUsers <= *maxUsers; numUsers *= 2 {

			testEvaluatorPrevMul(testContext, userList[:numUsers], t)
			testEvaluatorMul(testContext, userList[:numUsers], t)
			//testEvaluatorMulHoisted(testContext, userList[:numUsers], t)

			//testEvaluatorRot(testContext, userList[:numUsers], t)
			//testEvaluatorRotHoisted(testContext, userList[:numUsers], t)

			//testEvaluatorConj(testContext, userList[:numUsers], t)

			//testEvaluatorMulPtxt(testContext, userList[:numUsers], t)
		}
	}
}

func genTestParams(defaultParam Parameters, idset *mkrlwe.IDSet) (testContext *testParams, err error) {

	testContext = new(testParams)

	testContext.params = defaultParam

	testContext.kgen = NewKeyGenerator(testContext.params)

	testContext.skSet = mkrlwe.NewSecretKeySet()
	testContext.pkSet = mkrlwe.NewPublicKeyKeySet()
	testContext.rlkSet = mkrlwe.NewRelinearizationKeySet(defaultParam.Parameters)
	testContext.rtkSet = mkrlwe.NewRotationKeySet()
	testContext.cjkSet = mkrlwe.NewConjugationKeySet()

	// gen group sk, pk, rlk, rk
	// each group consists of 2 parties

	numParties := 4

	for id := range idset.Value {

		sk := make([]*mkrlwe.SecretKey, numParties)
		pk := make([]*mkrlwe.PublicKey, numParties)
		rlk := make([]*mkrlwe.RelinearizationKey, numParties)
		cjk := make([]*mkrlwe.ConjugationKey, numParties)
		rtks := make([]map[uint]*mkrlwe.RotationKey, numParties)

		for p := 0; p < numParties; p++ {
			sk[p], pk[p] = testContext.kgen.GenKeyPair(id)
			rlk[p] = testContext.kgen.GenRelinearizationKey(sk[p])
			cjk[p] = testContext.kgen.GenConjugationKey(sk[p])
			rtks[p] = testContext.kgen.GenDefaultRotationKeys(sk[p])
		}

		gsk := testContext.kgen.GenGroupSecretKey(sk)
		testContext.skSet.AddSecretKey(gsk)

		gpk := testContext.kgen.GenGroupPublicKey(pk)
		testContext.pkSet.AddPublicKey(gpk)

		grlk := testContext.kgen.GenGroupRelinKey(rlk)
		testContext.rlkSet.AddRelinearizationKey(grlk)

		gcjk := testContext.kgen.GenGroupConjKey(cjk)
		testContext.cjkSet.AddConjugationKey(gcjk)

		for idx, _ := range rtks[0] {
			rtk := make([]*mkrlwe.RotationKey, numParties)
			for p := 0; p < numParties; p++ {
				rtk[p] = rtks[p][idx]
			}
			grtk := testContext.kgen.GenGroupRotKey(rtk)
			testContext.rtkSet.AddRotationKey(grtk)
		}
	}

	testContext.ringQ = defaultParam.RingQ()

	if testContext.prng, err = utils.NewPRNG(); err != nil {
		return nil, err
	}

	testContext.encryptor = NewEncryptor(testContext.params)
	testContext.decryptor = NewDecryptor(testContext.params)

	testContext.evaluator = NewEvaluator(testContext.params)

	return testContext, nil

}

func newTestVectors(testContext *testParams, id string, a, b complex128) (msg *Message, ciphertext *Ciphertext) {

	params := testContext.params
	logSlots := testContext.params.LogSlots()

	msg = NewMessage(params)

	for i := 0; i < 1<<logSlots; i++ {
		msg.Value[i] = complex(utils.RandFloat64(real(a), real(b)), utils.RandFloat64(imag(a), imag(b)))
	}

	if testContext.encryptor != nil {
		ciphertext = testContext.encryptor.EncryptMsgNew(msg, testContext.pkSet.GetPublicKey(id))
	} else {
		panic("cannot newTestVectors: encryptor is not initialized!")
	}

	return msg, ciphertext
}

func testEncAndDec(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	skSet := testContext.skSet
	dec := testContext.decryptor

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], complex(-1, -1), complex(1, 1))
	}

	t.Run(GetTestName(testContext.params, "MKCKKSEncAndDec: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {

		for i := range userList {
			msgOut := dec.Decrypt(ctList[i], skSet)
			for j := range msgList[i].Value {
				delta := msgList[i].Value[j] - msgOut.Value[j]
				require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
			}
		}
	})

}

// Returns the ceil(log2) of the sum of the absolute value of all the coefficients

func testEvaluatorAdd(testContext *testParams, t *testing.T) {

	t.Run(GetTestName(testContext.params, "Evaluator/Add/CtCt/"), func(t *testing.T) {
		params := testContext.params
		msg1, ct1 := newTestVectors(testContext, "user1", complex(-1, -1), complex(1, 1))
		msg2, ct2 := newTestVectors(testContext, "user2", complex(-1, -1), complex(1, 1))
		msg3 := NewMessage(params)

		for i := range msg3.Value {
			msg3.Value[i] = msg1.Value[i] + msg2.Value[i]
		}

		user1 := "user1"
		user2 := "user2"
		idset1 := mkrlwe.NewIDSet()
		idset2 := mkrlwe.NewIDSet()

		idset1.Add(user1)
		idset2.Add(user2)

		ct3 := testContext.evaluator.AddNew(ct1, ct2)

		msg1Out := testContext.decryptor.Decrypt(ct1, testContext.skSet)
		msg2Out := testContext.decryptor.Decrypt(ct2, testContext.skSet)
		msg3Out := testContext.decryptor.Decrypt(ct3, testContext.skSet)

		for i := range msg1Out.Value {
			delta := msg1.Value[i] - msg1Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg2Out.Value {
			delta := msg2.Value[i] - msg2Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg3Out.Value {
			delta := msg3.Value[i] - msg3Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

	})

}

func testEvaluatorSub(testContext *testParams, t *testing.T) {

	t.Run(GetTestName(testContext.params, "Evaluator/Sub/CtCt/"), func(t *testing.T) {
		params := testContext.params
		msg1, ct1 := newTestVectors(testContext, "user1", complex(-1, -1), complex(1, 1))
		msg2, ct2 := newTestVectors(testContext, "user2", complex(-1, -1), complex(1, 1))
		msg3 := NewMessage(params)

		for i := range msg3.Value {
			msg3.Value[i] = msg1.Value[i] - msg2.Value[i]
		}

		user1 := "user1"
		user2 := "user2"
		idset1 := mkrlwe.NewIDSet()
		idset2 := mkrlwe.NewIDSet()

		idset1.Add(user1)
		idset2.Add(user2)

		ct3 := testContext.evaluator.SubNew(ct1, ct2)

		msg1Out := testContext.decryptor.Decrypt(ct1, testContext.skSet)
		msg2Out := testContext.decryptor.Decrypt(ct2, testContext.skSet)
		msg3Out := testContext.decryptor.Decrypt(ct3, testContext.skSet)

		for i := range msg1Out.Value {
			delta := msg1.Value[i] - msg1Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg2Out.Value {
			delta := msg2.Value[i] - msg2Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg3Out.Value {
			delta := msg3.Value[i] - msg3Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

	})

}

func testEvaluatorMul(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rlkSet := testContext.rlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	ptxt := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)
	ptxt2 := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)

	testContext.ringQ.NTT(ptxt, ptxt)
	testContext.ringQ.NTT(ptxt2, ptxt2)
	testContext.ringQ.MForm(ptxt2, ptxt2)
	testContext.ringQ.MulCoeffsMontgomery(ptxt, ptxt2, ptxt)
	testContext.ringQ.InvNTT(ptxt, ptxt)
	testContext.ringQ.DivRoundByLastModulusLvl(ptxt.Level(), ptxt, ptxt)
	ptxt.Coeffs = ptxt.Coeffs[:ptxt.Level()]

	t.Run(GetTestName(testContext.params, "MKMulAndRelin: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.MulRelinNew(ct, ct, rlkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes, testContext.skSet)

		testContext.ringQ.Sub(ptxtRes, ptxt, ptxtRes)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(imag(delta))))
		}

	})

}

func testEvaluatorPrevMul(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rlkSet := testContext.rlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	ptxt := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)
	ptxt2 := testContext.decryptor.DecryptToPtxt(ct, testContext.skSet)

	testContext.ringQ.NTT(ptxt, ptxt)
	testContext.ringQ.NTT(ptxt2, ptxt2)
	testContext.ringQ.MForm(ptxt2, ptxt2)
	testContext.ringQ.MulCoeffsMontgomery(ptxt, ptxt2, ptxt)
	testContext.ringQ.InvNTT(ptxt, ptxt)
	testContext.ringQ.DivRoundByLastModulusLvl(ptxt.Level(), ptxt, ptxt)
	ptxt.Coeffs = ptxt.Coeffs[:ptxt.Level()]

	t.Run(GetTestName(testContext.params, "MKPrevMulAndRelin: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.PrevMulRelinNew(ct, ct, rlkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes, testContext.skSet)

		testContext.ringQ.Sub(ptxtRes, ptxt, ptxtRes)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(imag(delta))))
		}

	})

}

func testEvaluatorRescale(testContext *testParams, t *testing.T) {

	t.Run(GetTestName(testContext.params, "Evaluator/Rescale/Single/"), func(t *testing.T) {
		params := testContext.params
		msg1, ct1 := newTestVectors(testContext, "user1", complex(-1, -1), complex(1, 1))
		msg2, ct2 := newTestVectors(testContext, "user2", complex(-1, -1), complex(1, 1))
		msg3 := NewMessage(params)

		constant := testContext.ringQ.Modulus[ct1.Level()]

		for i := range msg3.Value {
			msg3.Value[i] = msg1.Value[i] + msg2.Value[i]
		}

		user1 := "user1"
		user2 := "user2"
		idset1 := mkrlwe.NewIDSet()
		idset2 := mkrlwe.NewIDSet()

		idset1.Add(user1)
		idset2.Add(user2)

		ct3 := testContext.evaluator.AddNew(ct1, ct2)

		testContext.evaluator.MultByConst(ct3, constant, ct3)
		ct3.Scale *= float64(constant)
		testContext.evaluator.Rescale(ct3, params.Scale(), ct3)

		msg1Out := testContext.decryptor.Decrypt(ct1, testContext.skSet)
		msg2Out := testContext.decryptor.Decrypt(ct2, testContext.skSet)
		msg3Out := testContext.decryptor.Decrypt(ct3, testContext.skSet)

		for i := range msg1Out.Value {
			delta := msg1.Value[i] - msg1Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg2Out.Value {
			delta := msg2.Value[i] - msg2Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

		for i := range msg3Out.Value {
			delta := msg3.Value[i] - msg3Out.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+8, math.Log2(math.Abs(real(delta))))
		}

	})

}

func testEvaluatorRot(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rtkSet := testContext.rtkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]
	rot := int(utils.RandUint64()%uint64(2*params.N())) - params.N()

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKRotate: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		eval.DropLevel(ct, 1)
		ctRes := eval.RotateNew(ct, rot, rtkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			var delta complex128
			if rot > 0 {
				delta = msgRes.Value[i] - msg.Value[(i+rot)%len(msg.Value)]
			} else {
				delta = msg.Value[i] - msgRes.Value[(i-rot)%len(msg.Value)]
			}
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(imag(delta))))
		}
	})

}

func testEvaluatorConj(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	cjkSet := testContext.cjkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] = cmplx.Conj(msg.Value[j])
	}

	t.Run(GetTestName(testContext.params, "MKConjugate: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.ConjugateNew(ct, cjkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(imag(delta))))
		}
	})

}

func testEvaluatorMulHoisted(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rlkSet := testContext.rlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	t.Run(GetTestName(testContext.params, "MKMulAndRelinHoisted: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		eval.DropLevel(ct, 1)
		ctHoisted := eval.HoistedForm(ct)
		ctRes := eval.MulRelinHoistedNew(ct, ct, ctHoisted, nil, rlkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		ctRes2 := testContext.encryptor.EncryptMsgNewScale(msg, testContext.pkSet.GetPublicKey(userList[0]), ctRes.Scale)
		ctRes2 = eval.SubNew(ctRes2, ctRes)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes2, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(imag(delta))))
			require.GreaterOrEqual(t, float64(20), log2OfInnerSum(ctRes2.Level(), testContext.ringQ, ptxtRes))
		}
	})

}

func testEvaluatorRotHoisted(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rtkSet := testContext.rtkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.5/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]
	rot := 1 << int(utils.RandUint64()%uint64(params.logSlots-1))

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKRotateHoisted: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		eval.DropLevel(ct, 1)
		ctHoisted := eval.HoistedForm(ct)
		ctRes := eval.RotateHoistedNew(ct, rot, ctHoisted, rtkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			var delta complex128
			if rot > 0 {
				delta = msgRes.Value[i] - msg.Value[(i+rot)%len(msg.Value)]
			} else {
				delta = msg.Value[i] - msgRes.Value[(i-rot)%len(msg.Value)]
			}
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+11, math.Log2(math.Abs(imag(delta))))
		}
	})

}

func testEvaluatorMulPtxt(testContext *testParams, userList []string, t *testing.T) {

	params := testContext.params
	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i],
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)),
			complex(0.1/float64(numUsers), 1.0/float64(numUsers)))
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	pt := testContext.encryptor.EncodeMsgNew(msg)

	for j := range msg.Value {
		msg.Value[j] *= msg.Value[j]
	}

	t.Run(GetTestName(testContext.params, "MKMulPtxt: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		eval.DropLevel(ct, 1)
		ctRes := eval.MulPtxtNew(ct, pt)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(real(delta))))
			require.GreaterOrEqual(t, -math.Log2(params.Scale())+float64(params.LogSlots())+12, math.Log2(math.Abs(imag(delta))))
		}
	})

}
