#!/usr/bin/env python3
"""Bounded numerical rank completion with analytic Schur-complement derivatives.

Research tool for unpaired-scalar-decoding.md. Outputs are numerical candidates, never exact rank proofs.
Every hit stores the full instance, decoder, singular values and search receipt.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import least_squares


def decoder(x, W, d):
    n = W.shape[1]
    return np.einsum('sij,sab->iajb', x.reshape(len(W), d, d), W,
                     optimize=True).reshape(d*n, d*n)


def instance(n, w, d, seed, mode='unpaired'):
    rng = np.random.default_rng(seed)
    U = rng.standard_normal((d, n, n))
    permutation = np.arange(d)
    if mode == 'paired':
        assert d % 2 == 0
        # Match Fable's RNG sequence for the Gaussian paired controls.
        rng = np.random.default_rng(seed)
        for g in range(0, d, 2):
            U[g] = rng.standard_normal((n, n))
            U[g+1] = np.linalg.inv(U[g])
        permutation ^= 1
    if mode == 'toral':
        raw = [np.eye(n)] + [np.diag(rng.standard_normal(n)) for _ in range(w-1)]
    else:
        raw = [np.eye(n)] + [rng.standard_normal((n, n)) for _ in range(w-1)]
    Q = np.linalg.qr(np.stack([a.ravel() for a in raw], axis=1))[0]
    W = Q.T.reshape(w, n, n)
    tau = np.zeros((d*n, d*n))
    for g, h in enumerate(permutation):
        tau[g*n:(g+1)*n, h*n:(h+1)*n] = U[g]
    return tau, W, U


class Chart:
    def __init__(self, tau, W, d, target, x0, seconds):
        self.tau, self.W, self.d, self.target = tau, W, d, target
        self.n = W.shape[1]
        self.rank = len(tau)-target
        p, _, qt = np.linalg.svd(tau-decoder(x0, W, d))
        self.p1, self.p2 = p[:, :self.rank], p[:, self.rank:]
        self.q1, self.q2 = qt.conj().T[:, :self.rank], qt.conj().T[:, self.rank:]
        self.deadline = time.monotonic()+seconds
        self.last_x = None
        self.best_x = x0.copy()
        self.best_norm = float('inf')

    def evaluate(self, x):
        if time.monotonic() > self.deadline:
            raise TimeoutError('attempt time budget')
        if self.last_x is not None and np.array_equal(x, self.last_x):
            return
        m = self.tau-decoder(x, self.W, self.d)
        a, b = self.p1.conj().T@m@self.q1, self.p1.conj().T@m@self.q2
        c, e = self.p2.conj().T@m@self.q1, self.p2.conj().T@m@self.q2
        if self.rank:
            v = np.linalg.solve(a, b)
            z = np.linalg.solve(a.T, c.T).T
        else:
            v, z = np.zeros((0, self.target)), np.zeros((self.target, 0))
        self.residual = (e-c@v).ravel()
        left = (self.p2.conj().T-z@self.p1.conj().T).reshape(self.target, self.d, self.n)
        right = (self.q2-self.q1@v).reshape(self.d, self.n, self.target)
        self.jacobian = -np.einsum('uia,sab,jbv->uvsij', left, self.W, right,
                                  optimize=True).reshape(self.target**2, -1)
        self.last_x = x.copy()
        norm = np.linalg.norm(self.residual)
        if norm < self.best_norm:
            self.best_norm, self.best_x = float(norm), x.copy()

    def fun(self, x):
        self.evaluate(x)
        return self.residual

    def jac(self, x):
        self.evaluate(x)
        return self.jacobian

    def check_derivatives(self, x, rng):
        jac = self.jac(x).copy()
        errors = []
        for _ in range(3):
            direction = rng.standard_normal(len(x))
            direction /= np.linalg.norm(direction)
            epsilon = 1e-6
            finite = (self.fun(x+epsilon*direction)-self.fun(x-epsilon*direction))/(2*epsilon)
            exact = jac@direction
            errors.append(np.linalg.norm(finite-exact)/max(1, np.linalg.norm(exact)))
        assert max(errors) < 2e-5, errors
        return max(errors)


def run(tau, W, d, target, seed, restarts, seconds, cap, output, initial=None, evaluations=180):
    rng = np.random.default_rng(seed)
    records = []
    for attempt in range(restarts):
        x0 = rng.standard_normal(len(W)*d*d)*(.5 if attempt % 2 == 0 else 1.5)
        if initial is not None and attempt == 0:
            x0 = initial.ravel()+.15*rng.standard_normal(x0.size)
        x0 = np.clip(x0, -.95*cap, .95*cap)
        chart = Chart(tau, W, d, target, x0, seconds)
        derivative_error = chart.check_derivatives(x0, rng)
        started = time.monotonic()
        status = 'finished'
        try:
            sol = least_squares(chart.fun, x0, jac=chart.jac, bounds=(-cap, cap),
                                method='trf', tr_solver='exact', x_scale='jac',
                                ftol=1e-12, xtol=1e-12, gtol=1e-12, max_nfev=evaluations)
            status = sol.message
        except (TimeoutError, np.linalg.LinAlgError) as error:
            status = str(error)
        x = chart.best_x
        residual = tau-decoder(x, W, d)
        singular = np.linalg.svd(residual, compute_uv=False)
        scale = max(1., singular[0])
        tolerance = 1e-9*scale
        nullity = int(np.count_nonzero(singular < tolerance))
        pivot = chart.p1.T@residual@chart.q1
        record = dict(attempt=attempt, target=target, nullity=nullity,
                      coefficient_max=float(np.max(np.abs(x))),
                      schur_norm=chart.best_norm, seconds=time.monotonic()-started,
                      derivative_error=float(derivative_error), status=str(status),
                      tolerance=float(tolerance), singular_values=singular.tolist(),
                      pivot_condition=float(np.linalg.cond(pivot)) if len(pivot) else 1.)
        records.append(record)
        if record['schur_norm'] == min(r['schur_norm'] for r in records):
            np.savez_compressed(str(output)+'.best.npz', tau=tau, W=W,
                                kappa=x.reshape(len(W), d, d), singular_values=singular)
        print(json.dumps({k:v for k,v in record.items() if k != 'singular_values'}), flush=True)
        if nullity >= target:
            np.savez_compressed(str(output)+'.npz', tau=tau, W=W,
                                kappa=x.reshape(len(W), d, d), singular_values=singular)
            break
    output.with_suffix('.json').write_text(json.dumps(records, indent=2)+'\n')
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('w', type=int, nargs='?')
    parser.add_argument('d', type=int, nargs='?')
    parser.add_argument('target', type=int, nargs='?')
    parser.add_argument('--seed', type=int, default=20261113)
    parser.add_argument('--mode', choices=['unpaired','paired','toral','control'], default='unpaired')
    parser.add_argument('--restarts', type=int, default=6)
    parser.add_argument('--seconds', type=float, default=25)
    parser.add_argument('--cap', type=float, default=6)
    parser.add_argument('--evaluations', type=int, default=180)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        with np.load(args.verify, allow_pickle=False) as data:
            tau, W, kappa = data['tau'], data['W'], data['kappa']
            recorded = data['singular_values']
        assert W.ndim == kappa.ndim == 3
        w,n,_ = W.shape
        d = kappa.shape[1]
        assert W.shape == (w,n,n) and kappa.shape == (w,d,d)
        assert tau.shape == (d*n,d*n)
        assert all(np.isfinite(a).all() for a in (tau,W,kappa,recorded))
        explicit = sum(np.kron(kappa[s], W[s]) for s in range(w))
        assert np.allclose(explicit, decoder(kappa.ravel(), W, d), atol=1e-12)
        singular = np.linalg.svd(tau-explicit, compute_uv=False)
        assert np.allclose(singular, recorded, atol=1e-11, rtol=1e-10)
        tolerance = 1e-9*max(1.,singular[0])
        numerical_nullity = int(np.count_nonzero(singular < tolerance))
        print(json.dumps(dict(n=n,w=w,d=d,numerical_nullity=numerical_nullity,
                              coefficient_max=float(np.max(np.abs(kappa))),
                              tolerance=float(tolerance),
                              largest_small_singular=float(singular[-numerical_nullity]) if numerical_nullity else None,
                              smallest_large_singular=float(singular[-numerical_nullity-1]) if numerical_nullity<len(singular) else None)))
        return
    if any(x is None for x in (args.n,args.w,args.d,args.target,args.output)):
        parser.error('supply n w d target and --output, or use --verify')
    if not (1 <= args.w <= args.n**2 and 1 <= args.target <= args.n*args.d):
        parser.error('invalid block-space dimension or target nullity')
    if args.mode == 'toral' and args.w > args.n:
        parser.error('a diagonal block space has dimension at most n')
    initial = None
    if args.mode == 'control':
        assert (args.n,args.w,args.d,args.target) == (2,3,2,3)
        tau = np.array([[0,0,1,1],[0,0,0,1],[1,-1,0,0],[0,1,0,0]], dtype=float)
        W = np.array([[[1,0],[0,0]],[[0,0],[0,1]],[[0,1],[1,0]]], dtype=float)
        W[2] /= np.sqrt(2)
        initial = np.array([[[-1,1],[1,0]], [[0,1],[1,-1]],
                            [[0,0],[-np.sqrt(2),0]]])
    else:
        tau,W,_ = instance(args.n,args.w,args.d,args.seed,args.mode)
    print(json.dumps(vars(args), default=str), flush=True)
    run(tau,W,args.d,args.target,args.seed+731,args.restarts,args.seconds,args.cap,args.output,initial,args.evaluations)


if __name__ == '__main__':
    main()
