package mkbfv

import "mk-lattigo/mkrlwe"

import "github.com/stretchr/testify/require"
import "github.com/ldsec/lattigo/v2/rlwe"
import "github.com/ldsec/lattigo/v2/ring"
import "github.com/ldsec/lattigo/v2/utils"

import "fmt"
import "testing"
import "strconv"
import "math/big"
import "flag"

func GetTestName(params Parameters, opname string) string {
	return fmt.Sprintf("%slogN=%d/logQP=%d/levels=%d",
		opname,
		params.LogN(),
		params.LogQP(),
		params.MaxLevel(),
	)
}

var maxUsers = flag.Int("n", 8, "maximum number of parties")

var PN15QP880 = ParametersLiteral{
	LogN: 15,

	Q: []uint64{
		// 10 * 54 + 4 * 55
		0x3fffffffd60001,
		0x3fffffff6d0001,
		0x3fffffff550001,
		0x3fffffff360001,
		0x3fffffff000001,
		0x3ffffffef40001,
		0x3ffffffed30001,
		0x3ffffffe970001,
		0x3ffffffe800001,
		0x3ffffffe410001,

		0x7fffffffe90001,
		0x7fffffffbd0001,
		0x7fffffffaa0001,
		0x7fffffff9f0001,
	},

	QMul: []uint64{
		// 10 * 54 + 4 * 55
		0x3fffffffca0001,
		0x3fffffff5d0001,
		0x3fffffff390001,
		0x3fffffff2a0001,
		0x3ffffffefa0001,
		0x3ffffffed70001,
		0x3ffffffeaa0001,
		0x3ffffffe920001,
		0x3ffffffe790001,
		0x3ffffffe320001,

		0x7fffffffbf0001,
		0x7fffffffba0001,
		0x7fffffffa50001,
		0x7fffffff7e0001,
	},

	P: []uint64{
		// 30, 45, 60 x 2

		//0x3ffc0001, 0x3fde0001,

		//0x1fffffc20001, 0x1fffff980001,

		0xffffffffffc0001, 0xfffffffff840001,
	},
	T:     65537,
	Sigma: rlwe.DefaultSigma,
}

var PN14QP439 = ParametersLiteral{
	LogN: 14,

	Q: []uint64{
		// 6 x 53
		0x200000000e0001, 0x20000000140001,
		0x200000007c0001, 0x20000000820001,
		0x20000001360001, 0x20000001460001,
	},

	QMul: []uint64{
		// 6 x 53
		0x20000000280001, 0x20000000640001,
		0x200000010c0001, 0x20000001180001,
		0x20000001520001, 0x200000015e0001,
	},
	P: []uint64{
		// 30, 45, 60 x 2

		0x3ffc0001, 0x3fde0001,

		//0x1fffffc20001, 0x1fffff980001,

		//0xffffffffffc0001, 0xfffffffff840001,
	},
	T:     65537,
	Sigma: rlwe.DefaultSigma,
}

type testParams struct {
	params    Parameters
	ringQ     *ring.Ring
	ringP     *ring.Ring
	ringQMul  *ring.Ring
	ringR     *ring.Ring
	prng      utils.PRNG
	kgen      *KeyGenerator
	skSet     *mkrlwe.SecretKeySet
	pkSet     *mkrlwe.PublicKeySet
	rlkSet    *RelinearizationKeySet
	oldRlkSet *mkrlwe.RelinearizationKeySet
	rtkSet    *mkrlwe.RotationKeySet
	cjkSet    *mkrlwe.ConjugationKeySet
	encryptor *Encryptor
	decryptor *Decryptor
	evaluator *Evaluator
	idset     *mkrlwe.IDSet
}

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

func genTestParams(defaultParam Parameters, idset *mkrlwe.IDSet) (testContext *testParams, err error) {

	testContext = new(testParams)

	testContext.params = defaultParam

	testContext.kgen = NewKeyGenerator(testContext.params)
	testContext.evaluator = NewEvaluator(testContext.params)

	testContext.skSet = mkrlwe.NewSecretKeySet()
	testContext.pkSet = mkrlwe.NewPublicKeyKeySet()
	testContext.rlkSet = NewRelinearizationKeySet(defaultParam)
	testContext.oldRlkSet = mkrlwe.NewRelinearizationKeySet(defaultParam.Parameters)
	testContext.rtkSet = mkrlwe.NewRotationKeySet()
	testContext.cjkSet = mkrlwe.NewConjugationKeySet()

	numParties := 4

	for id := range idset.Value {

		sk := make([]*mkrlwe.SecretKey, numParties)
		pk := make([]*mkrlwe.PublicKey, numParties)
		rlk := make([]*RelinearizationKey, numParties)
		oldRlk := make([]*mkrlwe.RelinearizationKey, numParties)
		cjk := make([]*mkrlwe.ConjugationKey, numParties)
		rtks := make([]map[uint]*mkrlwe.RotationKey, numParties)

		for p := 0; p < numParties; p++ {
			sk[p], pk[p] = testContext.kgen.GenKeyPair(id)
			rlk[p] = testContext.kgen.GenRelinearizationKey(sk[p])
			oldRlk[p] = testContext.kgen.KeyGenerator.GenRelinearizationKey(sk[p])
			cjk[p] = testContext.kgen.GenConjugationKey(sk[p])
			rtks[p] = testContext.kgen.GenDefaultRotationKeys(sk[p])
		}

		gsk := testContext.kgen.GenGroupSecretKey(sk)
		testContext.skSet.AddSecretKey(gsk)

		gpk := testContext.kgen.GenGroupPublicKey(pk)
		testContext.pkSet.AddPublicKey(gpk)

		grlk := testContext.kgen.GenGroupRelinKey(rlk)
		testContext.rlkSet.AddRelinearizationKey(grlk)

		gOldRlk := testContext.kgen.KeyGenerator.GenGroupRelinKey(oldRlk)
		testContext.oldRlkSet.AddRelinearizationKey(gOldRlk)

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
	testContext.ringQMul = defaultParam.RingQMul()
	testContext.ringR = defaultParam.RingR()

	if testContext.prng, err = utils.NewPRNG(); err != nil {
		return nil, err
	}

	testContext.encryptor = NewEncryptor(testContext.params)
	testContext.decryptor = NewDecryptor(testContext.params)

	return testContext, nil

}

func TestMKBFV(t *testing.T) {

	//defaultParams := []ParametersLiteral{PN14QP439, PN15QP880}

	defaultParams := []ParametersLiteral{PN14QP439}

	for _, defaultParam := range defaultParams {
		params := NewParametersFromLiteral(defaultParam)

		userList := make([]string, *maxUsers)
		idset := mkrlwe.NewIDSet()

		for i := range userList {
			userList[i] = "user" + strconv.Itoa(i)
			idset.Add(userList[i])
		}

		testContext, _ := genTestParams(params, idset)

		testEncAndDec(testContext, userList, t)

		for numUsers := 2; numUsers <= *maxUsers; numUsers *= 2 {
			testEvaluatorAdd(testContext, userList[:numUsers], t)
			testEvaluatorSub(testContext, userList[:numUsers], t)
			testEvaluatorMul(testContext, userList[:numUsers], t)
			testEvaluatorPrevMul(testContext, userList[:numUsers], t)
			//testEvaluatorRot(testContext, userList[:numUsers], t)
			//testEvaluatorConj(testContext, userList[:numUsers], t)
		}
	}
}

func newTestVectors(testContext *testParams, id string, a, b int64) (msg *Message, ciphertext *Ciphertext) {

	params := testContext.params
	msg = NewMessage(params)

	for i := 0; i < params.N(); i++ {
		msg.Value[i] = int64(utils.RandUint64()/2)%(b-a) + a
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
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], -int64(params.T())/4, int64(params.T())/4)
	}

	t.Run(GetTestName(testContext.params, "MKBFVEncAndDec: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {

		for i := range userList {
			msgOut := dec.Decrypt(ctList[i], skSet)
			for j := range msgList[i].Value {
				delta := msgList[i].Value[j] - msgOut.Value[j]
				require.Equal(t, int64(0), delta, fmt.Sprintf("%v vs %v", msgList[i].Value[j], msgOut.Value[j]))
			}
		}
	})

}

func testEvaluatorAdd(testContext *testParams, userList []string, t *testing.T) {

	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], -100, -20)
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKBFVAdd: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := ct
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.Equal(t, int64(0), delta, fmt.Sprintf("%v: %v vs %v", i, msgRes.Value[i], msg.Value[i]))
		}

	})

}

func testEvaluatorSub(testContext *testParams, userList []string, t *testing.T) {

	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], -2, 2)
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.SubNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] -= msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKBFVSub: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := ct
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.Equal(t, int64(0), delta, fmt.Sprintf("%v vs %v", msgRes.Value[i], msg.Value[i]))
		}
	})

}

func testEvaluatorMul(testContext *testParams, userList []string, t *testing.T) {

	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rlkSet := testContext.rlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], 0, 2)
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
	ptxtR := testContext.ringR.NewPoly()
	ptxt2R := testContext.ringR.NewPoly()

	testContext.evaluator.conv.ModUpQtoR(ptxt, ptxtR)
	testContext.evaluator.conv.Rescale(ptxt2, ptxt2R)

	testContext.ringR.NTT(ptxtR, ptxtR)
	testContext.ringR.MForm(ptxtR, ptxtR)
	testContext.ringR.NTT(ptxt2R, ptxt2R)
	testContext.ringR.MulCoeffsMontgomery(ptxtR, ptxt2R, ptxtR)
	testContext.evaluator.conv.Quantize(ptxtR, ptxt, testContext.params.T())

	t.Run(GetTestName(testContext.params, "MKMulAndRelin: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.MulRelinNew(ct, ct, rlkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes, testContext.skSet)

		testContext.ringQ.Sub(ptxtRes, ptxt, ptxtRes)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.Equal(t, int64(0), delta, fmt.Sprintf("%v: %v vs %v", i, msgRes.Value[i], msg.Value[i]))
		}

	})

}

func testEvaluatorPrevMul(testContext *testParams, userList []string, t *testing.T) {

	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	rlkSet := testContext.oldRlkSet
	eval := testContext.evaluator

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], 0, 2)
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
	ptxtR := testContext.ringR.NewPoly()
	ptxt2R := testContext.ringR.NewPoly()

	testContext.evaluator.conv.ModUpQtoR(ptxt, ptxtR)
	testContext.evaluator.conv.Rescale(ptxt2, ptxt2R)

	testContext.ringR.NTT(ptxtR, ptxtR)
	testContext.ringR.MForm(ptxtR, ptxtR)
	testContext.ringR.NTT(ptxt2R, ptxt2R)
	testContext.ringR.MulCoeffsMontgomery(ptxtR, ptxt2R, ptxtR)
	testContext.evaluator.conv.Quantize(ptxtR, ptxt, testContext.params.T())

	t.Run(GetTestName(testContext.params, "MKPrevMulAndRelin: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.PrevMulRelinNew(ct, ct, rlkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)
		ptxtRes := testContext.decryptor.DecryptToPtxt(ctRes, testContext.skSet)

		testContext.ringQ.Sub(ptxtRes, ptxt, ptxtRes)

		for i := range msgRes.Value {
			delta := msgRes.Value[i] - msg.Value[i]
			require.Equal(t, int64(0), delta, fmt.Sprintf("%v: %v vs %v", i, msgRes.Value[i], msg.Value[i]))
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
	slots := eval.params.N() / 2

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], 0, 2)
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
		ctRes := eval.RotateNew(ct, rot, rtkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := 0; i < slots; i++ {
			var delta int64
			if rot > 0 {
				delta = msgRes.Value[i] - msg.Value[(i+rot)%slots]
			} else {
				delta = msg.Value[i] - msgRes.Value[(i-rot)%slots]
			}
			require.Equal(t, int64(0), delta)
		}

		for i := 0; i < slots; i++ {
			var delta int64
			if rot > 0 {
				delta = msgRes.Value[i+slots] - msg.Value[(i+rot)%slots+slots]
			} else {
				delta = msg.Value[i+slots] - msgRes.Value[(i-rot)%slots+slots]
			}
			require.Equal(t, int64(0), delta)
		}

	})

}

func testEvaluatorConj(testContext *testParams, userList []string, t *testing.T) {

	numUsers := len(userList)
	msgList := make([]*Message, numUsers)
	ctList := make([]*Ciphertext, numUsers)

	cjkSet := testContext.cjkSet
	eval := testContext.evaluator
	slots := eval.params.N() / 2

	for i := range userList {
		msgList[i], ctList[i] = newTestVectors(testContext, userList[i], 0, 2)
	}

	ct := ctList[0]
	msg := msgList[0]

	for i := range userList {
		ct = eval.AddNew(ct, ctList[i])

		for j := range msg.Value {
			msg.Value[j] += msgList[i].Value[j]
		}
	}

	t.Run(GetTestName(testContext.params, "MKConjugate: "+strconv.Itoa(numUsers)+"/ "), func(t *testing.T) {
		ctRes := eval.ConjugateNew(ct, cjkSet)
		msgRes := testContext.decryptor.Decrypt(ctRes, testContext.skSet)

		for i := 0; i < slots; i++ {
			delta := msgRes.Value[i] - msg.Value[(i+slots)]
			require.Equal(t, int64(0), delta)
		}

		for i := 0; i < slots; i++ {
			delta := msgRes.Value[i+slots] - msg.Value[i]
			require.Equal(t, int64(0), delta)
		}

	})

}
