# EMERG-001: Controlled-feedback synthetic experiment

**Question:** Does adaptive coupling improve resilience over uncoupled and fixed-coupling networks?

**Three conditions:** uncoupled, coupled, adaptive. All use identical seeded initial states, noise and a shock at one-third of the run. Dynamics are `dx=dt*(-0.4*x-k*L*x)+noise`, with L the symmetric normalized graph Laplacian. Adaptive k updates by `k=clip(k+dt*(0.6*min(mean(x*x),4)-0.15*k),0,2)`.

**Defaults:** N=100, steps=300, dt=.05, 12 paired seeds, ring/random topologies, coupling=.2/.6/1.0.

**Metrics:** mean squared error, final-window error, mean constraint violation for |x|>1, sustained recovery time below smoothed mean-square threshold 0.1, and final coupling gain.

**Analysis:** Compare paired differences within each topology and coupling level; report uncertainty, nonrecoveries, and negative findings. Follow up with tuned conventional feedback-control baselines and out-of-distribution disturbances.

**Limitations:** This is a toy dynamical simulation, not proof of strong emergence or a fundamental force. Adaptation is a proposed implementation, not uniquely derived from Wright's Law. No empirical data are included.
