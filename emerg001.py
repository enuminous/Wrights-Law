import argparse,csv,json
from pathlib import Path
import numpy as np

def run(seed,n=100,steps=300,coupling=.6,topology='ring'):
 r=np.random.default_rng(seed); A=np.zeros((n,n))
 if topology=='ring':
  for i in range(n): A[i,(i-1)%n]=A[i,(i+1)%n]=1
 else:
  A=np.triu((r.random((n,n))<6/(n-1)).astype(float),1);A+=A.T
 d=A.sum(1); inv=np.divide(1,np.sqrt(d),out=np.zeros_like(d),where=d>0);L=np.eye(n)-inv[:,None]*A*inv[None,:]
 initial=r.normal(0,.15,n); noise=r.normal(0,.08*np.sqrt(.05),(steps,n)); shock=r.normal(1,.15,n)
 out=[]
 for mode in ('uncoupled','coupled','adaptive'):
  x=initial.copy(); k=0 if mode=='uncoupled' else coupling; errors=[]; violations=[]
  for t in range(steps):
   if t==steps//3:x+=shock
   e=float(np.mean(x*x));errors.append(e);violations.append(float(np.mean(np.maximum(np.abs(x)-1,0))))
   x+=.05*(-.4*x-k*(L@x))+noise[t]
   if mode=='adaptive':k=float(np.clip(k+.05*(.6*min(e,4)-.15*k),0,2))
  recovery=None
  for t in range(steps//3+10,steps-10):
   if all(v<.1 for v in np.convolve(errors,np.ones(10)/10,'same')[t:steps-10]):recovery=(t-steps//3)*.05;break
  out.append(dict(seed=seed,topology=topology,coupling=coupling,mode=mode,mean_error=float(np.mean(errors)),final_error=float(np.mean(errors[-20:])),mean_violation=float(np.mean(violations)),recovery_time=recovery,final_gain=k))
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--seeds',type=int,default=12);p.add_argument('--n',type=int,default=100);p.add_argument('--steps',type=int,default=300);p.add_argument('--out',default='results.csv');a=p.parse_args()
 if a.seeds<1 or a.n<3 or a.steps<30:p.error('seeds>=1, n>=3, steps>=30')
 rows=[v for topology in ('ring','random') for k in (.2,.6,1.) for seed in range(a.seeds) for v in run(seed,a.n,a.steps,k,topology)]
 path=Path(a.out)
 with path.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 summary={mode:dict(mean_error=float(np.mean([x['mean_error'] for x in rows if x['mode']==mode]))) for mode in ('uncoupled','coupled','adaptive')}
 Path(str(path)+'.summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
