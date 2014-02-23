functor 
import 
   NtccInterpreter at '../src/NtccInterpreter.ozf'
export 
define 
   Lvars = [testVar
            rho
            alpha
            gamma
            beta
            w
            z
            y
            x
           ]
   Vars = {MakeRecord var Lvars} 
   Vars:::0#1000
   ConstraintSystems = [fd 
                       ]
   SimulationTime = 3 
   S = fun{$ parms( W1 Z1 Y1 X1)}
          when(proc{$ Root} Root.current.X1  >:  0  Root.current.Y1  >:  0    end
               next(
                  par( 
                     tell(proc{$ Root} Root.current.X1  =:  1    end)
                     tell(proc{$ Root} Root.current.Y1  =:  1    end)
                     tell(proc{$ Root} Root.current.Z1  =:  Root.current.Z1  +  1    end)
                     tell(proc{$ Root} Root.current.W1  =:  Root.current.W1  -  1    end)
                     ) 
                  ) 
              ) 
       end  
   DTest = fun{$ parms( TestVar1)}
              next(
                 tell(proc{$ Root} Root.current.TestVar1  =:  5    end)
                 ) 
           end  
   BoundedRep = fun{$ parms( Beta1)}
                   boundedrep(5 7 tell(proc{$ Root} Root.current.Beta1  =:  1    end)
                             ) 
                end  
   BoundedStar = fun{$ parms( Gamma1)}
                    boundedstar(5 8 tell(proc{$ Root} Root.current.Gamma1  =:  1    end)
                               ) 
                 end  
   Nextupn = fun{$ parms( Alpha1)}
                nextupn( 5 tell(proc{$ Root} Root.current.Alpha1  =:  1    end)
                       ) 
             end  
   WhenEver = fun{$ parms( Rho2 Alpha2)}
                 whenever(proc{$ Root} Root.current.Alpha2  >:  0    end
                          tell(proc{$ Root} Root.current.Rho2  =:  1    end)
                         ) 
              end  
   LocalVar = fun{$ parms( FV)}
                 next(
                    localvar(fun{$ parms( LV__FreshVar2)} nextupn( 2 tell(proc{$ Root} LV__FreshVar2  =:  6    end)
                                                                 ) 
                             end)  
                    ) 
              end  
   Inic = fun{$ parms( W1 Z1 Y1 X1)}
             par( 
                tell(proc{$ Root} Root.current.X1  =:  3    end)
                tell(proc{$ Root} Root.current.Y1  =:  3    end)
                tell(proc{$ Root} Root.current.Z1  =:  3    end)
                tell(proc{$ Root} Root.current.W1  =:  3    end)
                ) 
          end  
   System = par({Inic parms( x y z w)} {BoundedRep parms( beta)} {BoundedStar parms( gamma)} {Nextupn parms( alpha)} {LocalVar parms( testVar)} {DTest parms( testVar)} {S parms( x y z w)} )
 
   {NtccInterpreter.simulate [System] 
    Vars 
    SimulationTime 
    'p6c.txt' } 
end 
