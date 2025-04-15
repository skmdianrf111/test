pub(crate) mod srs;
pub(crate) mod util;

use crate::pcs::multilinear_kzg::{MultilinearKzgPCS, MultilinearKzgProof};
use crate::{
    pcs::{prelude::PCSError, PolynomialCommitmentScheme},
    BatchProof,
};
use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseMultilinearExtension, DenseUVPolynomial,
    MultilinearExtension, Polynomial,
};
use ark_poly_commit::kzg10::{Commitment, Powers, Randomness, UniversalParams, KZG10};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    sync::Arc,
    borrow::Borrow,
    end_timer, format, log2,
    marker::PhantomData,
    rand::{Rng, SeedableRng},
    start_timer,
    string::ToString,
    test_rng, vec,
    vec::Vec,
};
use merlin::Transcript;
use std::{borrow::Cow, collections::HashMap};
use transcript::IOPTranscript;

type F = <Bls12_381 as Pairing>::ScalarField;
type Poly = DensePolynomial<F>;
type KZG10Scheme = KZG10<Bls12_381, Poly>;
type MultiPoly<F> = HashMap<(usize, usize), F>;

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq, Eq)]
pub struct SamaritanProof {
    commitments: Vec<Commitment<Bls12_381>>,
    evaluations: Vec<F>,
}

pub struct SamaritanPCS<E: Pairing> {
    phantom: PhantomData<E>,
}

impl<E: Pairing> PolynomialCommitmentScheme<E> for SamaritanPCS<E> {
    // Parameters
    type ProverParam = UniversalParams<Bls12_381>;
    type VerifierParam = UniversalParams<Bls12_381>;
    type SRS = UniversalParams<Bls12_381>;
    // Polynomial and its associated types
    type Polynomial = DensePolynomial<F>;
    type ProverCommitmentAdvice = ();
    type Point = Vec<F>;
    type Evaluation = F;
    // Commitments and proofs
    type Commitment = Commitment<Bls12_381>;
    type Proof = SamaritanProof;
    type BatchProof = BatchProof<E, Self>;

    fn gen_srs_for_testing<R: Rng>(rng: &mut R, log_size: usize) -> Result<Self::SRS, PCSError> {
        let max_degree = 1 << (log_size+1);
        KZG10::<Bls12_381, Poly>::setup(max_degree, false, rng)
            .map_err(|e| PCSError::InvalidParameters(format!("Setup failed: {:?}", e)))
    }

    /// Trim the universal parameters to specialize the public parameters.
    /// Input both `supported_log_degree` for univariate and
    /// `supported_num_vars` for multilinear.
    fn trim(
        srs: impl Borrow<Self::SRS>,
        supported_degree: Option<usize>,
        supported_num_vars: Option<usize>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), PCSError> {
        unimplemented!();
    }

    fn commit(
        prover_param: impl Borrow<Self::ProverParam>,
        poly: &Self::Polynomial,
    ) -> Result<(Self::Commitment, Self::ProverCommitmentAdvice), PCSError> {
        let prover_param = prover_param.borrow();
        let commit_timer = start_timer!(|| "commit");

        let (comm, rand) = commit(prover_param, poly);
        end_timer!(commit_timer);
        Ok((comm, ()))
    }

    /// On input a polynomial `p` and a point `point`, outputs a proof for the
    /// same. This function does not need to take the evaluation value as an
    /// input.
    ///
    /// This function takes 2^{num_var +1} number of scalar multiplications over
    /// G1:
    /// - it prodceeds with `num_var` number of rounds,
    /// - at round i, we compute an MSM for `2^{num_var - i + 1}` number of G2
    ///   elements.
    fn open(
        pp: impl Borrow<Self::ProverParam>,
        f_hat: &Self::Polynomial,
        prover_advice: &Self::ProverCommitmentAdvice,
        z: &Self::Point,
    ) -> Result<Self::Proof, PCSError> {
        let mut f_hat_coeffs = f_hat.coeffs();
        let miu = z.len() as u32;
        let mut evaluations = vec![F::zero(); 1 << miu];
        for i in 0..(1 << miu) {
            let index = (0..miu)
                .map(|k| (i >> k) & 1)
                .fold(0, |acc, bit| (acc << 1) | bit);
            evaluations[index] = f_hat_coeffs[i];
        }
        println!("OK111");
        // println!("evaluations{:?}",evaluations);
        let f_poly = DenseMultilinearExtension::from_evaluations_vec(miu as usize, evaluations);
        open_internal::<E>(pp.borrow(), f_hat_coeffs, &f_poly, miu, z.to_vec())
    }

    /// Input a list of multilinear extensions, and a same number of points, and
    /// a transcript, compute a multi-opening for all the polynomials.
    fn multi_open(
        _prover_param: impl Borrow<Self::ProverParam>,
        _polynomials: Vec<Self::Polynomial>,
        _advices: &[Self::ProverCommitmentAdvice],
        _points: &[Self::Point],
        _evals: &[Self::Evaluation],
        _transcript: &mut IOPTranscript<E::ScalarField>,
    ) -> Result<Self::BatchProof, PCSError> {
        unimplemented!();
    }

    /// Verifies that `value` is the evaluation at `x` of the polynomial
    /// committed inside `comm`.
    ///
    /// This function takes
    /// - num_var number of pairing product.
    /// - num_var number of MSM
    fn verify(
        verifier_param: &Self::VerifierParam,
        commitment: &Self::Commitment,
        z: &Self::Point,
        value: &E::ScalarField,
        proof: &Self::Proof,
    ) -> Result<bool, PCSError> {
        verify_internal::<Bls12_381>(verifier_param, z.to_vec(), proof)
    }

    /// Verifies that `value_i` is the evaluation at `x_i` of the polynomial
    /// `poly_i` committed inside `comm`.
    fn batch_verify(
        verifier_param: &Self::VerifierParam,
        commitments: &[Self::Commitment],
        points: &[Self::Point],
        batch_proof: &Self::BatchProof,
        transcript: &mut IOPTranscript<E::ScalarField>,
    ) -> Result<bool, PCSError> {
        unimplemented!();
    }
}

fn commit(
    pp: &UniversalParams<Bls12_381>,
    f: &Poly,
) -> (Commitment<Bls12_381>, Randomness<F, Poly>) {
    let mut rng = test_rng();

    let degree = f.degree();
    let srs: Vec<_> = pp
        .powers_of_gamma_g
        .iter()
        .take(degree + 1)
        .map(|(_, g)| *g)
        .collect();

    let powers = Powers {
        powers_of_g: Cow::from(&pp.powers_of_g),
        powers_of_gamma_g: Cow::from(srs),
    };

    KZG10Scheme::commit(&powers, f, None, Some(&mut rng)).unwrap()
}

fn compute_f_hat<F: Field>(evaluations: &[F], num_vars: usize) -> Vec<F> {
    let n = num_vars;
    let mut f_hat_coeffs = vec![F::zero(); 1 << n];

    for i in 0..(1 << n) {
        let index = (0..n)
            .map(|k| (i >> k) & 1)
            .fold(0, |acc, bit| (acc << 1) | bit);
        f_hat_coeffs[i] = evaluations[index];
    }

    f_hat_coeffs
}

fn generate_ghat<F: Field>(f_coeffs: &[F], miu: u32) -> Vec<DensePolynomial<F>> {
    let n = 1 << miu; 
    let l = 1 << miu.ilog2(); 
    let m = n / l;

    let mut f_matrix: Vec<Vec<F>> = vec![vec![F::zero(); m]; l];
    // g_hat有L个，每个式子有m个系数，将f_hat的系数分成l*m的矩阵
    for i in 0..l {
        for j in 0..m {
            let index = i * m + j;
            f_matrix[i][j] = f_coeffs[index];
        }
    }

    let g_hat: Vec<DensePolynomial<F>> = f_matrix
        .iter()
        .map(|row| DensePolynomial::from_coefficients_vec(row.clone()))
        .collect();

    g_hat
}

fn compute_q<F: Field>(g_vec: &[DensePolynomial<F>], l: usize) -> MultiPoly<F> {
    let mut q_poly: MultiPoly<F> = HashMap::new();

    for (i, g_i) in g_vec.iter().enumerate().take(l) {
        let x_deg = i;
        for (y_deg, coeff) in g_i.coeffs.iter().enumerate() {
            if *coeff == F::zero() {
                continue;
            }
            let key = (x_deg, y_deg);
            *q_poly.entry(key).or_insert(F::zero()) += coeff;
        }
    }
    q_poly
}

fn compute_gtilde<F: Field>(
    f_poly: &DenseMultilinearExtension<F>,
    miu: u32,
    i: usize,
) -> DenseMultilinearExtension<F> {
    let n = 1 << miu; 
    let l = 1 << miu.ilog2(); 
    let m = n / l;
    let nu = log2(l) as usize;

    let i = i - 1;
    let i_binary: Vec<F> = (0..nu)
        .map(|j| {
            if (i >> (nu - 1 - j)) & 1 == 1 {
                F::one()
            } else {
                F::zero()
            }
        })
        .collect();
    // println!("i={}的二进制表示为:{:?}", i, i_binary);
    let g_tilde = f_poly.fix_variables(&i_binary);
    g_tilde
}

fn kron<F: Field>(v1: &Vec<F>, v2: &Vec<F>) -> Vec<F> {
    let mut result = Vec::with_capacity(v1.len() * v2.len());
    for x in v1 {
        for y in v2 {
            result.push(*x * *y); // 有限域上的乘法
        }
    }
    result
}

fn compute_psihat(z: &[F]) -> DensePolynomial<F> {
    let mut psi_hat = DensePolynomial::from_coefficients_vec(vec![F::one()]);
    let mu = z.len();
    let mut phi = vec![F::one()-z[0], z[0]];
    for i in 1 .. mu{
        let next_vector = vec![F::one()-z[i], z[i]];
        phi = kron(&phi, &next_vector);
    }
    phi.reverse();
    psi_hat = DensePolynomial::from_coefficients_vec(phi);
    psi_hat
}

fn compute_phat(q_poly: MultiPoly<F>, gamma: F) -> DensePolynomial<F> {
    let max_y = q_poly.keys().map(|&(_, y_deg)| y_deg).max().unwrap_or(0);
    let mut p_hat_coeffs = vec![F::zero(); max_y + 1];

    for (&(x_deg, y_deg), &coeff) in &q_poly {
        let mut term = coeff;
        for _ in 0..x_deg {
            term *= gamma;
        }
        p_hat_coeffs[y_deg] += term;
    }
    DensePolynomial {
        coeffs: p_hat_coeffs,
    }
}

fn compute_r<F: Field>(q_poly: MultiPoly<F>, gamma: F) -> MultiPoly<F>
where
    F: std::ops::MulAssign + std::ops::AddAssign + Copy + PartialEq,
{
    let mut r_poly: MultiPoly<F> = HashMap::new();
    for (&(x_deg, y_deg), &coeff) in &q_poly {
        if x_deg == 0 {
            continue;
        }
        let mut gamma_power = F::one();
        for _ in 0..(x_deg - 1) {
            gamma_power *= gamma;
        }
        for k in 0..x_deg {
            let r_coeff = coeff * gamma_power;
            *r_poly.entry((k, y_deg)).or_insert(F::zero()) += r_coeff;
            gamma_power *= gamma;
        }
    }
    r_poly
}

fn compute_r_hat<F: Field>(r_poly: MultiPoly<F>, m: usize) -> DensePolynomial<F>
where
    F: std::ops::MulAssign + std::ops::AddAssign + Copy + PartialEq,
{
    let max_deg = r_poly
        .keys()
        .map(|&(x_deg, y_deg)| m * x_deg + y_deg)
        .max()
        .unwrap_or(0);
    let mut r_hat_coeffs = vec![F::zero(); max_deg + 1];
    for (&(x_deg, y_deg), &coeff) in &r_poly {
        let degree = m * x_deg + y_deg;
        r_hat_coeffs[degree] += coeff;
    }
    DensePolynomial {
        coeffs: r_hat_coeffs,
    }
}

fn polynomial_mul<F: Field>(poly1: &DensePolynomial<F>, poly2: &DensePolynomial<F>) -> DensePolynomial<F> {
    let mut result_coeffs = vec![F::zero(); poly1.degree() + poly2.degree() + 1]; // 结果多项式的系数

    // 对每个多项式的系数进行相乘并累加到结果
    for (i, &coeff1) in poly1.coeffs.iter().enumerate() {
        for (j, &coeff2) in poly2.coeffs.iter().enumerate() {
            result_coeffs[i + j] += coeff1 * coeff2; // 累加到对应指数的系数上
        }
    }

    DensePolynomial::from_coefficients_vec(result_coeffs)
}

fn open_internal<E: Pairing>(
    pp: &UniversalParams<Bls12_381>,
    f_hat_coeffs: &[F],
    f_poly: &DenseMultilinearExtension<F>,
    miu: u32,
    z: Vec<F>,
) -> Result<SamaritanProof, PCSError> {
    let open_timer = start_timer!(|| format!("open mle with {} variable", miu));

    let v = f_poly
        .evaluate(&z)
        .ok_or_else(|| PCSError::InvalidParameters("Failed to evaluate f_poly at z".to_string()))?;
    let n = 1 << miu; 
    let l = 1 << miu.ilog2(); 
    let m = n / l;
    let k = log2(m) as usize;

    let mut commitments = Vec::new();
    let mut evaluations = Vec::new();
    // 第二步
    // 先计算g_hat
    let g_hat = generate_ghat(&f_hat_coeffs, miu);
    // for (i, g) in g_hat.iter().enumerate() {
    //     // println!("g_hat{}: {:?}", i + 1, g.coeffs);
    // }
    // 再计算Q(X,Y)
    let q_poly = compute_q(&g_hat, l); /////////
    println!("OK222");
    // 第三步
    // 先分出z_x，z_y
    let z_x = &z[z.len() - k..];
    let z_y = &z[..miu as usize - k];
    // println!("z{:?}",z);
    // println!("z_y{:?}",z_y);
    // println!("z_x{:?}", z_x);
    // 再计算v_i
    let mut v_vec: Vec<F> = Vec::with_capacity(l);
    for i in 1..=l {
        let g_tilde = compute_gtilde(f_poly, miu, i);
        // println!("g_tilde{:?}", g_tilde);
        let v_i = g_tilde.evaluate(&z_x);
        v_vec.push(v_i.unwrap());
        // println!("v_{} = tilde_g_{}({:?}) = {:?}", i, i, z_x, v_i);
    }
    println!("OK333");

    // 第四步
    // 先计算v_hat
    let v_hat = DensePolynomial::from_coefficients_vec(v_vec.clone());
    println!("OK444111");
    // 再计算ψ_hat
    let psi_hat = compute_psihat(&z_y);
    println!("OK444222");
    // println!("psi_hat(X) = {:?}", psi_hat.coeffs);
    // let psi_hat_z = compute_psihat(&z);
    // println!("v_psi_z(X) = {:?}", psi_hat_z.coeffs);
    let v_psi = polynomial_mul(&v_hat ,&psi_hat);
    println!("OK444333");
    // // let v_psi = &v_hat * &psi_hat;
    // let f_hat = DensePolynomial::from_coefficients_vec(f_hat_coeffs.to_vec().clone());
    // let test = polynomial_mul(&psi_hat_z , &f_hat);
    println!("OK444444");
    // let test = &psi_hat_z * &f_hat;
    let mut a_coeffs = vec![F::zero(); v_psi.degree() - l + 1];
    let mut b_coeffs = vec![F::zero(); l - 1];
    println!("START111");
    for i in l..=v_psi.degree() {
        a_coeffs[i - l] = v_psi.coeffs[i];
    }

    if (v == Fr::from(v_psi.coeffs[l - 1].into_bigint())) {
        println!("YES111");
    } else {
        println!("NO111")
    }
    for i in 0..l - 1 {
        b_coeffs[i] = v_psi.coeffs[i];
    }
    
    // if (v == Fr::from(test.coeffs[n - 1].into_bigint())) {
    //     println!("YES333");
    // } else {
    //     println!("NO333")
    // }
    
    let a_hat = DensePolynomial::from_coefficients_vec(a_coeffs);
    let b_hat = DensePolynomial::from_coefficients_vec(b_coeffs);
    // let test = v_psi.coeffs[l - 1].into_bigint();
    // println!("v_psi(X) = {:?}", v_psi.coeffs);
    // println!("a_hat(X) = {:?}", a_hat.coeffs);
    // println!("test = {:?}",test.coeffs);
    // println!("v = {:?}", v);
    // // println!("v_psi.coeffs(l-1)={:?}", test);
    // println!("b_hat(X) = {:?}", b_hat.coeffs);

    // 第五步
    let (cm_v, _) = commit(pp, &v_hat);
    let (cm_a, _) = commit(pp, &a_hat);
    commitments.push(cm_v);
    commitments.push(cm_a);

    let mut transcript = Transcript::new(b"MyKZGPCS");

    transcript.append_u64(b"v_vec_len", v_vec.len() as u64);

    let mut cm_v_bytes = Vec::new();
    cm_v.serialize_uncompressed(&mut cm_v_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_v", &cm_v_bytes);
    let mut cm_a_bytes = Vec::new();
    cm_a.serialize_uncompressed(&mut cm_a_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_a", &cm_a_bytes);

    let mut gamma_bytes = [0u8; 32];
    transcript.challenge_bytes(b"gamma", &mut gamma_bytes);
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(gamma_bytes);
    let gamma = Fr::rand(&mut rng);

    // 第七步
    // 计算v(γ)
    let v_gamma = v_hat.evaluate(&gamma);
    // println!("v_gamma = v_jian({:?}) = {:?}", gamma, v_gamma);

    let p_hat = compute_phat(q_poly.clone(), gamma);
    // println!("p_hat(X) = Q(gamma, X) = {:?}", p_hat);

    // 计算r_hat
    let r_poly = compute_r(q_poly, gamma);
    let r_hat = compute_r_hat(r_poly, m);

    // 第八步

    let psi_hat_y = compute_psihat(z_x);
    let p_psi = &p_hat * &psi_hat_y;
    // 计算h_hat,u_hat
    let mut h_coeffs = vec![F::zero(); p_psi.degree() - m + 1];
    let mut u_coeffs = vec![F::zero(); m - 1];

    for i in m..=p_psi.degree() {
        h_coeffs[i - m] = p_psi.coeffs[i];
    }
    if (v_gamma == Fr::from(p_psi.coeffs[m - 1].into_bigint())) {
        println!("YES222");
    } else {
        println!("NO222")
    }
    for i in 0..m - 1 {
        u_coeffs[i] = p_psi.coeffs[i];
    }

    let h_hat = DensePolynomial::from_coefficients_vec(h_coeffs);
    let u_hat = DensePolynomial::from_coefficients_vec(u_coeffs);

    // println!("p_psi(X) = {:?}", p_psi.coeffs);
    // println!("h_hat(X) = {:?}", h_hat.coeffs);
    // println!("v_gamma = {:?}", v_gamma);
    // println!(
    //     "p_psi.coeffs(m-1)={}",
    //     Fr::from(p_psi.coeffs[m - 1].into_bigint())
    // );
    // println!("u_hat(X) = {:?}", u_hat.coeffs);

    // 第九步
    let (cm_p, _) = commit(pp, &p_hat);
    let (cm_r, _) = commit(pp, &r_hat);
    let (cm_h, _) = commit(pp, &h_hat);
    commitments.push(cm_p);
    commitments.push(cm_r);
    commitments.push(cm_h);

    let mut cm_p_bytes = Vec::new();
    cm_v.serialize_uncompressed(&mut cm_p_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_p", &cm_p_bytes);
    let mut cm_r_bytes = Vec::new();
    cm_a.serialize_uncompressed(&mut cm_r_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_r", &cm_r_bytes);
    let mut cm_h_bytes = Vec::new();
    cm_a.serialize_uncompressed(&mut cm_h_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_h", &cm_h_bytes);

    let mut beta_bytes = [0u8; 32];
    transcript.challenge_bytes(b"beta", &mut beta_bytes);
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(beta_bytes);
    let beta = Fr::rand(&mut rng);

    // 第十一步
    // 先分别取逆
    // 构造 t(X)
    let p_hat_inv_coeff: Vec<F> = p_hat.coeffs.iter().rev().cloned().collect();
    let p_hat_inv = DensePolynomial::from_coefficients_vec(p_hat_inv_coeff);

    // term1 = X^(m-1) * p_hat_inv
    let mut term1_coeff = vec![F::zero(); (m - 1) + p_hat_inv.degree() + 1];
    for i in 0..=p_hat_inv.degree() {
        term1_coeff[i + (m - 1)] = p_hat_inv.coeffs[i];
    }
    let term1 = DensePolynomial::from_coefficients_vec(term1_coeff);

    let u_hat_inv_coeff: Vec<F> = u_hat.coeffs.iter().rev().cloned().collect();
    let u_hat_inv = DensePolynomial::from_coefficients_vec(u_hat_inv_coeff);

    // term2 = beta * X^(m-2) * u_hat_inv
    let mut term2_coeff = vec![F::zero(); (m - 2) + u_hat_inv.degree() + 1];
    for i in 0..=u_hat_inv.degree() {
        term2_coeff[i + (m - 2)] = beta * u_hat_inv.coeffs[i];
    }
    let term2 = DensePolynomial::from_coefficients_vec(term2_coeff);
    // println!("term2 = {:?}", term2.coeffs);

    let b_hat_inv_coeff: Vec<F> = b_hat.coeffs.iter().rev().cloned().collect();
    let b_hat_inv = DensePolynomial::from_coefficients_vec(b_hat_inv_coeff);

    // term3 = beta^2 * X^(l-2) * b_hat_inv
    let beta_2 = beta * beta;
    let mut term3_coeff = vec![F::zero(); (l - 2) + b_hat_inv.degree() + 1];
    for i in 0..=b_hat_inv.degree() {
        term3_coeff[i + (l - 2)] = beta_2 * b_hat_inv.coeffs[i];
    }
    let term3 = DensePolynomial::from_coefficients_vec(term3_coeff);
    // println!("term3 = {:?}", term3.coeffs);

    // 确保多项式加法时系数对齐
    let max_degree = std::cmp::max(
        term1.degree(),
        std::cmp::max(term2.degree(), term3.degree()),
    );
    let mut t_coeffs = vec![F::zero(); max_degree + 1];

    // 手动累加系数
    for i in 0..=term1.degree() {
        t_coeffs[i] += term1.coeffs[i];
    }
    for i in 0..=term2.degree() {
        t_coeffs[i] += term2.coeffs[i];
    }
    for i in 0..=term3.degree() {
        t_coeffs[i] += term3.coeffs[i];
    }

    let t_poly = DensePolynomial::from_coefficients_vec(t_coeffs);
    // println!("t(X) = {:?}", t_poly.coeffs);

    let (cm_t, _) = commit(pp, &t_poly);
    commitments.push(cm_t);

    let mut cm_t_bytes = Vec::new();
    cm_t.serialize_uncompressed(&mut cm_t_bytes)
        .map_err(|e| PCSError::SerializationError(e))?;
    transcript.append_message(b"cm_t", &cm_t_bytes);

    let mut delta_bytes = [0u8; 32];
    transcript.challenge_bytes(b"delta", &mut delta_bytes);
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(delta_bytes);
    let delta = Fr::rand(&mut rng);

    // println!("delta: {:?}", delta);

    let delta_inv = delta.inverse().unwrap();
    let test2 = delta * delta_inv;
    // println!("delta*delta_inv= {}", test2);

    let del_inv = delta.inverse().unwrap();
    let delta_m1 = del_inv.pow(&[(m - 1) as u64]);
    let delta_m2 = del_inv.pow(&[(m - 2) as u64]);
    let delta_l2 = del_inv.pow(&[(l - 2) as u64]);

    let f_hat = DensePolynomial::from_coefficients_vec(f_hat_coeffs.to_vec());
    let f_delta = f_hat.evaluate(&delta);
    // println!("f_hat(delta) = {:?}", f_delta);

    let p_delta = p_hat.evaluate(&delta);
    // println!("p_hat(delta) = {:?}", p_delta);

    let h_delta = h_hat.evaluate(&delta);
    // println!("h_hat(delta) = {:?}", h_delta);

    let v_delta = v_hat.evaluate(&delta);
    // println!("v_hat(delta) = {:?}", v_delta);

    let a_delta = a_hat.evaluate(&delta);
    // println!("a_hat(delta) = {:?}", a_delta);

    let u_delta = u_hat.evaluate(&delta);
    // println!("u_delta={:?}", u_delta);

    let b_delta = b_hat.evaluate(&delta);
    // println!("b_delta = {:?}", b_delta);

    let t_delta_inv = delta_m1 * p_delta + beta * delta_m2 * u_delta + beta_2 * delta_l2 * b_delta;
    // println!("t(delta^{{-1}}) = {:?}", t_delta_inv);

    let eval_slice: Vec<F> = vec![
        delta,
        t_delta_inv,
        f_delta,
        p_delta,
        h_delta,
        v_delta,
        a_delta,
        v,
        v_gamma,
        beta,
        F::from(m as u64),
        F::from(l as u64),
    ];
    evaluations.extend_from_slice(&eval_slice);
    end_timer!(open_timer);
    Ok(SamaritanProof {
        commitments,
        evaluations,
    })
}

fn verify_internal<E: Pairing>(
    verifier_param: &UniversalParams<Bls12_381>,
    z: Vec<F>,
    proof: &SamaritanProof,
) -> Result<bool, PCSError> {
    let verify_timer = start_timer!(|| "verify");

    let delta = proof.evaluations[0];
    let t_delta_inv = proof.evaluations[1];
    let f_delta = proof.evaluations[2];
    let p_delta = proof.evaluations[3];
    let h_delta = proof.evaluations[4];
    let v_delta = proof.evaluations[5];
    let a_delta = proof.evaluations[6];
    let v = proof.evaluations[7];
    let v_gamma = proof.evaluations[8];
    let beta = proof.evaluations[9];
    let m_f = proof.evaluations[10];
    let l_f = proof.evaluations[11];

    let m: usize = m_f.into_bigint().as_ref()[0] as usize;
    let l: usize = l_f.into_bigint().as_ref()[0] as usize;

    let delta_inv = delta
        .inverse()
        .ok_or_else(|| PCSError::InvalidParameters("Delta inverse failed".to_string()))?;
    let delta_m1 = delta_inv.pow(&[(m - 1) as u64]);
    let delta_m2 = delta_inv.pow(&[(m - 2) as u64]);
    let delta_l2 = delta_inv.pow(&[(l - 2) as u64]);

    let mu = z.len();
    let k = log2(m) as usize;
    let z_y = &z[..mu - k];
    let z_x = &z[mu - k..];
    let psi_hat_y = compute_psihat(z_x);
    let psi_delta_y = psi_hat_y.evaluate(&delta);
    let delta_m = delta.pow(&[m as u64]);
    let delta_m_1 = delta.pow(&[(m - 1) as u64]);
    let u_delta = p_delta * psi_delta_y - delta_m * h_delta - v_gamma * delta_m_1;
    // println!("u_verify{:?}", u_delta);
    let psi_hat_x = compute_psihat(z_y);
    let psi_delta_x = psi_hat_x.evaluate(&delta);
    let delta_l = delta.pow(&[l as u64]);
    let delta_l_1 = delta.pow(&[(l - 1) as u64]);
    let b_delta = v_delta * psi_delta_x - delta_l * a_delta - v * delta_l_1;
    // println!("b_verify{:?}", b_delta);
    let rhs = delta_m1 * p_delta + beta * delta_m2 * u_delta + beta * beta * delta_l2 * b_delta;
    // println!("rhs = {}", rhs);
    // println!("t_delta_inv = {}", t_delta_inv);
    let mut res = false;

    if t_delta_inv != rhs {
        println!("验证失败");
    } else {
        res = true;
        println!("验证成功");
    }
    end_timer!(verify_timer);
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_poly::univariate::DensePolynomial;
    use ark_std::{
        test_rng,
        vec::Vec,
        UniformRand,
    };
    use env_logger;
    use crate::pcs::multilinear_kzg::{MultilinearKzgPCS, MultilinearKzgProof};
    use ark_bls12_381::{Fr as Bls12_381Fr};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use ark_std::sync::Arc;

   

    #[test]
    fn test_method() {
        env_logger::init();
        let mut lambda = 128;
        let miu = 18 as usize;
        let mut rng = test_rng();
        let pp =
            SamaritanPCS::<Bls12_381>::gen_srs_for_testing(&mut rng, miu).expect("生成 SRS 失败");

        let evaluations: Vec<Fr> = (1..=1 << miu).map(|i| Fr::from(i as u64)).collect();
        let poly =
            DenseMultilinearExtension::from_evaluations_vec(miu as usize, evaluations.clone());

        let f_hat_coeffs = compute_f_hat(&evaluations, miu);
        let f_hat = DensePolynomial::from_coefficients_vec(f_hat_coeffs.clone());

        let (commitment, _) = SamaritanPCS::<Bls12_381>::commit(&pp, &f_hat).expect("承诺失败");

        let z: Vec<F> = (0..miu).map(|_| F::rand(&mut rng)).collect();
        // let mut z: Vec<F> = vec![F::from(1), F::from(0), F::from(1), F::from(0)];
        let proof = SamaritanPCS::<Bls12_381>::open(&pp, &f_hat, &(), &z).expect("打开承诺失败");
        // let v = poly.evaluate(&z);
        // println!("v={:?}",v);
        let is_valid =
            SamaritanPCS::<Bls12_381>::verify(&pp, &commitment, &z, &proof.evaluations[0], &proof)
                .expect("验证失败");

        assert!(is_valid, "证明验证未通过");
        println!("承诺、打开和验证测试成功！");
    }

    #[test]
    fn test_multilinear_kzg_timing() {
        type E = Bls12_381;
        type F = Bls12_381Fr;
        // env_logger::init();
        let mut rng = test_rng();
        let num_vars = 18; // 变量数量

        let params = MultilinearKzgPCS::<E>::gen_srs_for_testing(&mut rng, num_vars).expect("MultilinearKzg SRS 生成失败");

        let (prover_param, verifier_param) = MultilinearKzgPCS::<E>::trim(&params, None, Some(num_vars)).expect("参数修剪失败");

        let evaluations: Vec<F> = (0..(1 << num_vars)).map(|_| F::rand(&mut rng)).collect();
        let poly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(num_vars, evaluations));

        let z: Vec<F> = (0..num_vars).map(|_| F::rand(&mut rng)).collect();
        let eval = poly.evaluate(&z).unwrap();

        let commit_timer = start_timer!(|| "MultilinearKzgPCS commit");
        let (commitment, _) = MultilinearKzgPCS::<E>::commit(&prover_param, &poly).expect("MultilinearKzg 承诺失败");
        end_timer!(commit_timer);

        let open_timer = start_timer!(|| "MultilinearKzgPCS open");
        let proof = MultilinearKzgPCS::<E>::open(&prover_param, &poly, &(), &z).expect("MultilinearKzg 打开承诺失败");
        end_timer!(open_timer);

        let verify_timer = start_timer!(|| "MultilinearKzgPCS verify");
        let is_valid = MultilinearKzgPCS::<E>::verify(&verifier_param, &commitment, &z, &eval, &proof)
            .expect("MultilinearKzg 验证失败");
        end_timer!(verify_timer);

        assert!(is_valid, "MultilinearKzg 证明验证未通过");
        println!("MultilinearKzgPCS 承诺、打开和验证测试成功！");
    }
}
