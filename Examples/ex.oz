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
   S = fun{$ parms( X1 Y1 Z1 W1)}
          when(proc{$ Root} Root.current.X1  >:  0    end
               next(
                  par( 
                     tell(proc{$ Root} Root.current.X1  =:  Root.residual.X1  -  1    end)
                     tell(proc{$ Root} Root.current.Y1  =:  Root.residual.Y1  +  1    end)
                     tell(proc{$ Root} Root.current.Z1  =:  Root.residual.Z1    end)
                     tell(proc{$ Root} Root.current.W1  =:  Root.residual.W1    end)
                     ) 
                  ) 
              ) 
       end  
   BoundedStar = fun{$ parms( Gamma1)}
                    boundedstar(5 8 tell(proc{$ Root} Root.current.Gamma1  =:  1    end)
                               ) 
                 end  
   BoundedRep = fun{$ parms( Beta1)}
                   boundedrep(5 7 tell(proc{$ Root} Root.current.Beta1  =:  1    end)
                             ) 
                end  
   Nextupn = fun{$ parms( Alpha1)}
                nextupn( 5 tell(proc{$ Root} Root.current.Alpha1  =:  1    end)
                       ) 
             end  
   Inic = fun{$ parms( X1 Y1 Z1 W1)}
             par( 
                tell(proc{$ Root} Root.current.X1  =:  3    end)
                tell(proc{$ Root} Root.current.Y1  =:  3    end)
                tell(proc{$ Root} Root.current.Z1  =:  3    end)
                tell(proc{$ Root} Root.current.W1  =:  3    end)
                ) 
          end  
   Sump = fun{$ parms( X1 Y1 Z1 W1)}
             sum( 
                {S parms( X1 Y1 Z1 W1)} {S parms( X1 Z1 Y1 W1)} {S parms( W1 X1 Y1 Z1)} ) 
          end  
   System = par({Inic parms( x y z w)} {Nextupn parms( alpha)} {BoundedStar parms( gamma)} {Sump parms( x y z w)} )
 
   {NtccInterpreter.simulate [System] 
    Vars 
    SimulationTime 
    'exc.txt' } 
end 
