%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Authors:  Carlos Olarte              %%
%%          Michell Guzmán C.          %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

functor
   
import
   FD
   OS
   Space
   Open
   Browser
   Combinador
  % Combinator
export
   simulate: Simulate
define
   


   %% CloneVars
   fun{CloneVars R}
      thread {Record.map R fun{$ X}		       
                              if {FD.is X} then
                                 {FD.int {FD.reflect.dom X}}
                              else
                                 if {Record.is X} then
                                    {CloneVars X}
                                 elseif {List.is X} then
                                    thread {Record.toList {CloneVars {List.toTuple t X}}} end
                                 else
                                    X
                                 end
                              end                   
                           end
             }   end
      
   end
   %% End CloneVars


   fun {Execute Procs Vars ResidualVars LocalList}

      %% Variable definitions
      S
      Ctr 
     
      
      ResidualPort
      ResidualProcs
      Unless_wait
      AbortUnlessPort
      AbortUnlessProcs
      Store
      AbortResult
      %% End variable definitions
    

      fun{GetResidual L}
         case L of get | _ then nil
         [] H | get | _ then H | nil
         [] H | T   then H | {GetResidual T}
         end
      end


      fun{MakeAbort L}
         case L of abort | finish | _ then 1
         [] abort | unless | _ then 2
         [] unless | abort | _ then 2
         [] unless | finish | _ then 3
         [] finish | _ then  0
       %  [] _ | _ then 0
         else

            0
         end
      end

         
      

      proc{MakeSum P}
         {Space.inject S proc{$ Root}
                            {Combinador.'cond'
                             {Record.map P
                              fun{$ when(C P)}
                                 fun{$}
                                    {C Root}
                                    proc{$}
                                       {Send Ctr P}
                                    end
                                 end
                              end
                             }
                             proc{$}
                                skip
                             end
                            }
                         end    
         }
      end
      
      
      proc{MakePar Port P}
         {Record.forAll P proc{$ Pi} {Send Port Pi} end}
      end

      fun{MakeBoundedRep I L P}
         if I==L then
            [{MakeNextRec L P}]
         else
            {MakeNextRec I P}|{MakeBoundedRep I+1 L P}
         end	    
      end  
          
      fun {MakeNextRec N P}
         if N == 0 then
            P
         else
            next({MakeNextRec N-1 P})
         end
      end

      fun{MakeBoundedStar I L P}
         fun{RandLimit X Y}
            X+{OS.rand} mod ((Y-X)+1)
         end
      in
         {MakeNextRec {RandLimit I L} P}
      end

      
      proc {MakeStar P L}
         I = {OS.rand}
         TimeU
         Proc
      in
         TimeU = {Int.'mod' I L}
         Proc = {MakeNextRec TimeU P}
         {Send Ctr Proc}
      end

      
   
      fun{ProcCtr}
         Stream
      in
         thread
            for Proc in Stream do	 
               case Proc of 
                  tell(P) then {Space.inject S P} 
               [] when(C P) then thread {Space.inject S proc{$ Root} cond{C Root} then 
                                                                        {Send Ctr P}
                                                                     else skip 
                                                                     end
                                                        end} end
               [] next(P) then {Send ResidualPort P}             
                  
               [] unless(C P) then                
                  proc{ExecuteUnless}
                     {Space.inject S proc{$ Root}
                                        cond {C Root} then skip
                                        [] skip then
                                           {Send ResidualPort P}
                                        end
                                     end}	
                  end
               in
                  {Send AbortUnlessPort unless}
                  thread
                     if Unless_wait== unit then
                        {ExecuteUnless}
                        {Space.ask S _} 
                        {Send ResidualPort get} 
                     end
                  end	                   
               [] rep(_) then {Send Ctr Proc.1} {Send ResidualPort Proc}
               [] star(P L) then {MakeStar P L}        
               [] par(_ ...) then {MakePar Ctr Proc} 
               [] sum(_ ...) then {MakeSum Proc}
               [] boundedrep(I L P) then
                  {MakePar Ctr {List.toTuple t {MakeBoundedRep I-1 L-1 P}}}
               [] boundedstar(I L P) then {Send Ctr {MakeBoundedStar I-1 L-1 P}}
               [] nextupn(N P) then {Send Ctr {MakeNextRec N-1 P}}
               [] whenever(C P) then {Send Ctr rep(when(C P))}          
               [] abort then {Send AbortUnlessPort abort}
               [] localvar(F) then                     
                  {Space.inject S  proc{$ Root}
                                      Nvar1
                                      Process
                                   in
                                      Nvar1 = {Root.current.addvar}
                                      Process = {F Nvar1}
                                      {Root.current.sendToPort Process}
                                         
                                   end}    
               else
                  {Browser.browse 'default'#Proc}		
               end	 
            end
         end
         {NewPort Stream}

      end
      
      
    
      fun{CreateSpace Vars}
         {Space.new proc{$ Root}

                       %% Variable definitions
                       Counter ListLVar
                       LocalVars
                       EndStream = _
                       StreamTailPortObject  		       
                       CounterPortObject		       
                       UnlessVar                       
                       Processes
                       EndStream2 = _


                       AbortUnlessPortLocal
                       AbortUnlessProcsLocal
                       %% End variable definitions
                       
                       fun{AddVarSpace}
                          New_var
                       in
                          New_var = {NewVar}              
                          New_var
                       end
                         
                                                            
                       fun{NewPortObject Behavior Init}
                          proc{MsgLoop S1 State}
                             case S1 of Msg|S2 then
                                {MsgLoop S2 {Behavior Msg State}}
                             [] nil then skip
                             end
                          end
                          Stream
                       in
                          thread {MsgLoop Stream Init} end
                          {NewPort Stream}
                       end
                       
                       fun{Counter}
                          {NewPortObject fun{$ Msg State}
                                            case Msg of add(N) then
                                               State + N                   	 
                                            [] getCount(N) then
                                               N=State 
                                               N     
                                            end
                                         end 0}
                       end
		       
                       fun{StreamTail}
                          {NewPortObject fun{$ Msg State}
                                            case Msg of changeStreamTail(N) then
                                               N
                                            [] getStreamTail(N) then
                                               N=State
                                               N
                                            end			   
                                         end start}
                       end	       
                     
                   
                     
                       fun{NewVar}
                          Next = {FD.decl}
                          Count
                          Result
                          NuevoFin=_
                       in   
                          {Send CounterPortObject add(1)}
                          {Send CounterPortObject getCount(Count)}
                        
                          {Send StreamTailPortObject getStreamTail(Result)}
                         
                          Result = Next|NuevoFin
                  
                          {Send StreamTailPortObject changeStreamTail(NuevoFin)}

                          Count          
                       end
		             

                       proc{TerminateStream}
                          Result
                       in
                          {Send StreamTailPortObject getStreamTail(Result)}
                          Result = nil
                          {Send StreamTailPortObject changeStreamTail(Result)}
                       end


                       fun{PortSpaceS}
                          Stream
                       in
                          thread
                             for Proc in Stream do	 
                                case Proc of
                                   tell(P) then
                                   {P Root}
                                [] when(C P) then                           
                                   cond {C Root} then
                                      {Send LocalPort P}
                                   else
                                      skip
                                   end
                                [] next(P) then                                 
                                   {Send ResidualLocalPort P}
                                   %% Unless not available yet
                                [] unless(C P) then
                                   proc{ExecuteUnless}
                              %     thread   {Browser.browse wtf#AbortUnlessProcsLocal} end
                                      cond {C Root} then {Browser.browse 'Skip executed'} skip
                                      [] skip then
                                       %  {Browser.browse 'Skip not executed'}
                                         {Send ResidualLocalPort P}
                                       %  {Browser.browse 'Process on residual port'}
                                      end
                                   end
                                in
                                   {Send AbortUnlessPortLocal unless}
                                   thread
                                      if UnlessVar== unit then
                                         {ExecuteUnless}
                                         {Space.waitStable} 
                                         {Send ResidualLocalPort get}
                                         {TerminateStream}
                                         {ResidualProcesses}
                                      end
                                   end	                                  
				   
                                [] rep(_) then {Send LocalPort Proc.1} {Send ResidualLocalPort Proc}
                                [] par(_ ...) then {MakePar LocalPort Proc}
                                [] sum(_ ...) then
                                   {Combinador.'cond'
                                    {Record.map Proc
                                     fun{$ when(C Proc)}
                                        fun{$}
                                           {C Root}
                                           proc{$}
                                              {Send LocalPort Proc}
                                           end
                                        end
                                     end
                                    }
                                    proc{$}
                                       skip
                                    end
                                   }
                                [] boundedrep(I L P) then
                                   {MakePar LocalPort {List.toTuple t {MakeBoundedRep I-1 L-1 P}}}
                                [] boundedstar(I L P) then {Send LocalPort {MakeBoundedStar I-1 L-1 P}}
                                [] nextupn(N P) then {Send LocalPort {MakeNextRec N-1 P}}
                                [] whenever(C P) then {Send LocalPort rep(when(C P))}
                                   %% not available yet
                                [] abort then {Send AbortUnlessPortLocal abort}
                                [] localvar(F)
                                then
                                   Nvar1                                   
                                   Process
                                in
                                   Nvar1 = {AddVarSpace}
                                   Process = {F Nvar1}
                                   {Send LocalPort Process}                                   
                                else
                                   {Browser.browse 'default'#Proc}
                                end
                             end
                          end
                          {NewPort Stream}
                       end

                       LocalPort
                       
                       ResidualLocalPort
                       LocalPortStream

                       proc{SendToPort P}                       
                          {Send LocalPort P}
                       end
                       
                       proc{SendMessage Msg}
                          case Msg of get then
                             {Send ResidualLocalPort get}
                          [] finish then
                             {Send AbortUnlessPortLocal finish}
                          end
                       end

                       proc{ResidualProcesses}
                          Residual = {GetResidual LocalPortStream}
                       in
                          EndStream2 = Residual|nil 
                       end

                       fun{LocalAbort}
                          AbortResult
                       in
                          AbortResult = {MakeAbort AbortUnlessProcsLocal}
                          AbortResult
                       end

                       fun{ReturnUnlessWait}
                          UnlessVar
                       end

                       proc{UnlessWait}
                          UnlessVar = unit
                       end

                       proc{AskSpace}
                          {Space.waitStable}
                          %skip
                       end

                       fun{ReturnAbort}
                          {MakeAbort AbortUnlessProcsLocal}
                       end
                 
                    in
                       LocalPort = {PortSpaceS}
                       ResidualLocalPort = {NewPort LocalPortStream}                  
		                                                
                       
                       LocalVars = vars(list:ListLVar terminate:TerminateStream addvar:AddVarSpace sendToPort:SendToPort sendMsg:SendMessage residualLocalProcs:ResidualProcesses rProc:Processes abortProc:LocalAbort returnUnlessWait:ReturnUnlessWait unlessWait:UnlessWait askSpace:AskSpace)  
                                                           
                       Root = vars(residual: {CloneVars ResidualVars}                                
                                   current: {CloneVars {Adjoin Vars LocalVars}}
                                  )

                       AbortUnlessPortLocal = {NewPort AbortUnlessProcsLocal}
                       
                       ListLVar = {Append LocalList EndStream}
                       
                       Processes = start | EndStream2
                   
                       CounterPortObject = {Counter}
                       {Send CounterPortObject add({List.length LocalList})}
                     
                       StreamTailPortObject = {StreamTail}
                       {Send StreamTailPortObject changeStreamTail(EndStream)}                                    
                       
                    end}
      end

 
   in


      S = {CreateSpace Vars} 

   
      Ctr = {ProcCtr}


      thread
         if Unless_wait== unit then
            if {MakeAbort AbortUnlessProcs}==2 then
               skip
            elseif {MakeAbort AbortUnlessProcs} == 3 then
               skip
            else
               {Space.ask S _}	      
               {Send ResidualPort get}
            end
         end
      end

      ResidualPort = {NewPort ResidualProcs}
      AbortUnlessPort = {NewPort AbortUnlessProcs}

     
      for P in Procs do {Send Ctr P} end

     
  

      thread  {Space.inject S proc{$ Root}
                                 if {Root.current.returnUnlessWait}== unit then
             
                                    if {Root.current.abortProc} == 2 then
                                     
                                       skip
                                    elseif {Root.current.abortProc} == 3 then
                                     
                                       skip
                                    else
                                     
                                       {Root.current.sendMsg get}
                                        
                                       {Root.current.terminate}

                                       {Root.current.residualLocalProcs}
                                    end
                                 end
                              end}
      end
       


      {Time.delay 3}


      

      %% Prueba

      {Space.inject S proc{$ Root}
                         {Root.current.unlessWait}
                         {Root.current.sendMsg finish}
                      end}

      %%
      
      {Send AbortUnlessPort finish}
      AbortResult = {MakeAbort AbortUnlessProcs}
      
      Unless_wait=unit

      Store = store(procs: {GetResidual ResidualProcs}
                    residual: {Space.merge {Space.clone S}})


  
      result(Store AbortResult)
   end

   %% End execute

   %% Simulate
   proc{Simulate Procs Vars Steps FileName}
      
      fun{FreshVarsDoms InputList}
         Length = {List.length InputList}
         OutputList = {List.make Length}
         {List.forAll OutputList proc{$ X} X={FD.decl} end}
      in
         OutputList
      end
      LRes
      File


      fun{SRec P V Res I LocalList}
         if I==0 then nil
         else
            Store = {Execute P V Res LocalList}
          
         in          
            if Store.2 == 1 then nil
            elseif Store.2 == 2 then nil
            elseif Store.1.residual.current.abortProc == 1 then nil
            elseif Store.1.residual.current.abortProc == 2 then nil
            else

		
               {Record.forAllInd Vars proc{$ X I}
                                         %% Por ahora uso isDet
                                         if {Value.isDet Store.1.residual.current.X} then					    
                                            {File write(vs:Store.1.residual.current.X)}
                                         else
                                            {File write(vs:dom)}
                                         end					
                                         {File write(vs:";")}
                                      end
               }
               {File write(vs:"\n")}
            in		
               Store.1.residual.current|{SRec {List.append Store.1.procs Store.1.residual.current.rProc.2.1} Vars Store.1.residual.current I-1 {FreshVarsDoms Store.1.residual.current.list}}              
            end
         end            
      end
    
   in      
      {OS.srand 0}


      File={New Open.file
            init(name:  FileName
                 flags: [write create truncate]
                )}

 
      {Record.forAllInd Vars proc{$ I X}
                                {File write(vs:I#";")}
                             end
      }
      {File write(vs:"\n")}
      LRes = {SRec Procs Vars nil Steps [{FD.decl}]}
      {File close}
   
   end
   
   %% End simulate
   
end
