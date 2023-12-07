fn power(a:i32, b:i32)->i32{
    if b==0{
        return 1
    }
    else if b==1 {
        return a
    }
    else if b%2==0{
        let c= power(a,b/2);
        return c*c
    }
    else {
        let c=power(a,(b-1)/2);
        return c*c*a
    }
}
pub struct Primefields{
    base:i32 
}

impl Primefields{
    pub fn new(base:i32) -> Primefields{
        Primefields{
            base:base
        }
    }
    fn add(&self,a:i32,b:i32) -> i32{
        return (a+b)%self.base
    }
    fn inv_add(&self,a:i32) -> i32{
        return self.base-a
    }
    fn mult(&self,a:i32,b:i32) -> i32{
        return (a*b)%self.base
    }
    fn inv_mult(&self,a:i32) -> i32{
        return (power(a,self.base-2))%self.base
    }
    fn power(&self,a:i32,e:i32) -> i32{
        let mut f=e%(self.base-1);
        if f<0{
            f=f+self.base-1;
        }
        return (power(a,f))%self.base
    }
}


pub struct Extension{
    p:Primefields,
    num:i32,
    rule: Vec<i32>
}

fn print_in_extension(v:Vec<i32>){
    for i in 0..v.len(){
    println!("+{0} i {1}",v[i],i)}

}
impl Extension{
    pub fn new(p:Primefields,num:i32,rule:Vec<i32>)-> Extension{
        Extension{
            p:p,
            num:num,
            rule:rule
        }
    }
    pub fn add(&self,a:Vec<i32>,b:Vec<i32>) -> Vec<i32>{
        let mut v=vec![];
        for i in 0..a.len(){
            v.push(self.p.add(a[i],b[i]))
        }
        return v;
    }
    pub fn inv_add(&self,a:Vec<i32>) -> Vec<i32>{
        let mut v=vec![];
        for i in 0..a.len(){
            v.push(self.p.base-a[i])
        }
        return v;
    }
    pub fn mult(&self,a:Vec<i32>,b:Vec<i32>)->Vec<i32>{
        let mut v=vec![];
        for i in 0..(a.len()+b.len()-1){
            let mut cnt=0;
            let mut st=0;
            if i>b.len()-1{
                st=i-b.len()+1;
            }
            for j in st..a.len(){
                if i>=j {
                cnt=cnt+a[j]*b[i-j]}
            }
            v.push(cnt);
        }
        let length=a.len()+b.len()-1;
        for k in length-self.rule.len()..(length){
            if length-k>=self.rule.len(){
                for p in 0..self.rule.len()-1{
                    v[length-k-self.rule.len()+p]=v[length-k-self.rule.len()+p]+self.rule[self.rule.len()-1-p]*v[length-k-1];
                }
            }
        }
        let mut w=vec![];
        for c in 0..a.len(){
            let mut r=v[c]%self.p.base;
            if r<0{
                r+=self.p.base;
            }
            w.push(r);
        }
        return w;
    }
    pub fn power(&self,a:Vec<i32>, b:i32)->Vec<i32>{
        if b==0{
            let mut v=vec![0;a.len()];
            v[0]=1;
            return v
        }
        else if b==1 {
            return a
        }
        else if b%2==0{
            let c= self.power(a.clone(),b/2);
            let d=c.clone();
            return self.mult(c,d)
        }
        else {
            let c=self.power(a.clone(),b-1);
            return self.mult(c,a.clone())
        }
    }

    pub fn inv_mult(&self,a:Vec<i32>)->Vec<i32>{
        let c=power(self.p.base,self.num);
        return self.power(a,c-2);
    }
}

fn main(){
    let p=Primefields::new(5);
    let a:Vec<i32>=vec![1,-1,-1];
    let e=Extension::new(p,2,a);
    let a1=vec![1,2];
    let a2=vec![3,3];
    print_in_extension(e.mult(a1.clone(),a2));
    print_in_extension(e.inv_mult(a1.clone()));
    print_in_extension(e.mult(e.inv_mult(a1.clone()),a1.clone()));
}