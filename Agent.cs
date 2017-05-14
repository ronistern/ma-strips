using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class Agent
    {
        public static bool allPrivateLandmarks = false;
        //List<StateInfo> allStates = null;
        Dictionary<StateInfo, int> hashOfStates = null;
        public List<Action> allActionsWithProjectionAction;
        public string name = "";
        List<GroundedPredicate> publicGoals = null;
        public  Dictionary<string, Action> mapActionNameToAction = null;
        List<GroundedPredicate> privateGoals = null;
        HashSet<GroundedPredicate> AllLocalGoals = null;
        public List<Action> relaxtionPlan;
        public HashSet<GroundedPredicate> AchievedFacts = null;
        public List<GroundedPredicate> relaxGoals = new List<GroundedPredicate>();
        List<string> MyPlan = null;
        Dictionary<GroundedPredicate, int> predicateGrade;
        HashSet<GroundedPredicate> currentLayer;
        public bool[][] initialVectors;
        public List<Action> m_actions = null;
        public State orginalStartState = null;
        public HashSet<GroundedPredicate> orginaPredicates = null;
        public HashSet<GroundedPredicate> orginaPublicPredicates = null;
        public List<Action> orginalActions = null;
        public List<Action> orginalpublicActions = null;
        public List<Action> orginalprivateActions = null;
        public List<Action> publicActions = null;
        public List<Action> privateActions = null;
        public Problem problem;
        public Domain domain;
        public int level = 0;
        Dictionary<int, StateInfo> mapToState = null;
        Dictionary<GroundedPredicate, int> hspGraph = null;
        Dictionary<GroundedPredicate, Action> PreferablesActions = null;
        Dictionary<GroundedPredicate, List<Action>> canGetPredicate = null;
        public HashSet<GroundedPredicate> Predicates = null;
        public HashSet<GroundedPredicate> PublicPredicates = null;
        public State startState = null;
        private State aproximationState = null;
        //public State aproximatePublicState = null;
        public List<GroundedPredicate> goal = null;
        List<Landmark> discoverdLandmark = null;
        List<Landmark> localDiscoverdLandmark = null;
        public List<Landmark> publicRelevantLandmark = null;
        public List<GroundedPredicate> allGoals=new List<GroundedPredicate>();
        public List<GroundedPredicate> tmpGoals=new List<GroundedPredicate>();
        public List<Landmark> publicLandmarks = null;
        public List<Order> orderList = null;
        Queue<Landmark> standByPublicLandmarks = null;
        Queue<Landmark> standByPrivateLandmarks = null;
        public Queue<Landmark> localPublicLandmarks = null;
        Queue<Landmark> localPrivateLandmarks = null;
        //HashSet<GroundedPredicate> OtherCanGet = null;//new HashSet<GroundedPredicate>();
        HashSet<GroundedPredicate> iCanGet = null;//new HashSet<GroundedPredicate>();
        HashSet<GroundedPredicate> privateCanGet = null;
        HashSet<Action> temporalActionsNontGet = null;
        List<Action> temporalActionsCanGet = null;
        List<Action> PossibleBefore = null;
        Landmark exploreLandmarks = null;
        HashSet<GroundedPredicate> publiciCanGet;
        Dictionary<GroundedPredicate, int> disTable;
        HashSet<GroundedPredicate> m_AchievedSet = null;
        List<Action> cantDonePrivateAction = null;
        bool isMyLandmarks = false;
        List<int> indexOfGoals = null;
        public List<Order> ReasonableOrdering = null;
        public Dictionary<Predicate, HashSet<Predicate>> MutuallyExclusive = null;
        public Dictionary<Predicate, List<Action>> allFactsWithActAchieve = null;
        public Dictionary<GroundedPredicate, GroundedPredicate> mapGpToArtificial;
        public Dictionary<GroundedPredicate, GroundedPredicate> ArtificialToPrivate;
        public HashSet<GroundedPredicate> invariantPredicate = null;

        public Agent(Problem p, Domain d, List<Action> actions, List<Action> m_pablicActions, List<Action> m_privateActions,
            HashSet<GroundedPredicate> m_Predicates, HashSet<GroundedPredicate> m_PublicPredicates, State m_startState, List<GroundedPredicate> m_Goal, string m_Name, List<Action> m_ProjectionPublicAction, Dictionary<Predicate, HashSet<Predicate>> lInvariants)
        {
            problem = p;
            domain = d;
            m_actions = actions;
            publicActions = m_pablicActions;
            privateActions = m_privateActions;
            Predicates = m_Predicates;
            PublicPredicates = m_PublicPredicates;
            startState = m_startState;
            //orginalStartState = m_startState;
            goal = m_Goal;
            tmpGoals=new List<GroundedPredicate>(m_Goal);
            name = m_Name;
            aproximationState = new State(startState);

            discoverdLandmark = new List<Landmark>();
            localDiscoverdLandmark = new List<Landmark>();
            publicLandmarks = new List<Landmark>();
            orderList = new List<Order>();
            standByPublicLandmarks = new Queue<Landmark>();
            standByPrivateLandmarks = new Queue<Landmark>();
            localPublicLandmarks = new Queue<Landmark>();
            localPrivateLandmarks = new Queue<Landmark>();
            privateCanGet = new HashSet<GroundedPredicate>();
            publicRelevantLandmark = new List<Landmark>();
            MyPlan = new List<string>();
            //allStates = new List<StateInfo>();
            hashOfStates = new Dictionary<StateInfo, int>();
            allActionsWithProjectionAction = m_ProjectionPublicAction;
            MutuallyExclusive = lInvariants;

            /* DirectoryInfo di = new DirectoryInfo(@"C:\project\Planning 2 new\PDDLTEST\temp\");
             foreach (FileInfo fi in di.GetFiles())
                 if ((fi.Name.StartsWith("dT") || fi.Name.StartsWith("pT")))// && fi.Name.EndsWith(".pddl"))
                     fi.Delete();

             d.WriteSimpleDomain(@"C:\project\Planning 2 new\PDDLTEST\temp\dT.pddl");
             */
            /*  foreach (GroundedPredicate gp in aproximationState.Predicates)
              {
                  if (PublicPredicates.Contains(gp))
                  {
                      aproximatePublicState.AddPredicate(gp);
                  }
              }*/
            invariantPredicate = new HashSet<GroundedPredicate>();

            HashSet<GroundedPredicate> truePredicateEffect = new HashSet<GroundedPredicate>();
            HashSet<GroundedPredicate> FalsePredicateEffect = new HashSet<GroundedPredicate>();
            foreach (Action act in actions)
            {
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (!gp.Negation)
                    {
                        truePredicateEffect.Add(gp);
                    }
                    else
                    {
                        FalsePredicateEffect.Add(gp);
                    }
                }
            }
            foreach (GroundedPredicate predicate in m_Predicates)
            {

                if (!predicate.Negation)
                {
                    if (!truePredicateEffect.Contains(predicate) && !FalsePredicateEffect.Contains((GroundedPredicate)predicate.Negate()))
                    {
                        invariantPredicate.Add(predicate);
                    }
                }
                else
                {
                    if (!truePredicateEffect.Contains((GroundedPredicate)predicate.Negate()) && !FalsePredicateEffect.Contains(predicate))
                    {
                        invariantPredicate.Add(predicate);
                    }
                }

            }
            CalPublicfactsGoals();

            foreach (Action act in m_actions)
            {
                if (publicActions.Contains(act))
                    act.isPublic = true;
            }
        }

        public Agent(Agent agent)
        {
            //problem = agent.problem;
            // domain = agent.domain;
            m_actions = agent.m_actions;
            publicActions = agent.publicActions;
            privateActions = agent.privateActions;
            Predicates = agent.Predicates;
            PublicPredicates = agent.PublicPredicates;
            startState = agent.startState;
            goal = agent.goal;
            name = agent.name;
            MyPlan = new List<string>(agent.MyPlan);
            //discoverdLandmark = agent.discoverdLandmark;
            //orderList = agent.orderList;
            aproximationState = new State(agent.aproximationState);
            // aproximatePublicState = new State(agent.aproximatePublicState);
            // publicRelevantLandmark = agent.publicRelevantLandmark;

        }
        public void saveInfo()
        {
            orginalStartState = startState;
            orginaPredicates = Predicates;
            orginaPublicPredicates = PublicPredicates;
            orginalActions = m_actions;
            orginalpublicActions = publicActions;
            orginalprivateActions = privateActions;
        }
        public List<Action> GetUnPosibalePrivateAction(List<Action> actions)
        {
            WhatICanGetWithMyPrivate();
            List<Action> UnPosibalePrivateAction = new List<Action>();
            foreach(Action act in actions)
            {
                if (!Contains(privateCanGet, act.HashPrecondition))
                    UnPosibalePrivateAction.Add(act);
            }
            return UnPosibalePrivateAction;
        }
        public void GoBack()
        {
            startState = orginalStartState;
            Predicates = orginaPredicates;
            PublicPredicates = orginaPublicPredicates;
            m_actions = orginalActions;
            publicActions = orginalpublicActions;
            privateActions = orginalprivateActions;
        }

        public List<GroundedPredicate> GetPublicInvariante()
        {
            List<GroundedPredicate> ans = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in invariantPredicate)
            {
                if (PublicPredicates.Contains(gp))
                {
                    ans.Add(gp);
                }
            }
            return ans;
        }
        public void UpdateInvariant(List<GroundedPredicate> publicInvariant)
        {
            List<GroundedPredicate> dell = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in invariantPredicate)
            {
                if (PublicPredicates.Contains(gp))
                {
                    if (!publicInvariant.Contains(gp))
                    {
                        dell.Add(gp);
                    }
                }
            }
            foreach (GroundedPredicate dellItem in dell)
            {
                invariantPredicate.Remove(dellItem);
            }
        }
        public bool[] GetVectors(int stateNumber)
        {
            //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;
            StateInfo oldState = mapToState[stateNumber]; 
            return oldState.landmarksVector;
        }
        public bool PossibleInTheInitial(List<Action> actions)
        {
            foreach (Action act in actions)
            {
                if (Contains(privateCanGet, act.HashPrecondition))
                    return true;
            }
            return false;
        }
        public void InitMutex()
        {
            //MutuallyExclusive = domain.IdentifyInvariants(m_actions);
            MutuallyExclusive =  domain.IdentifyInvariants(allActionsWithProjectionAction);
        }

        public GroundedPredicate GetGoal()
        {
            GroundedPredicate tmp;
            if(tmpGoals.Count>0)
            {
                tmp=tmpGoals.ElementAt(0);
                allGoals.Add(tmp);
                tmpGoals.Remove(tmp);
                if (PublicPredicates.Contains(tmp))
                {
                    return tmp;
                }
                else
                {
                    return new GroundedPredicate(Domain.FALSE_PREDICATE);
                }
            }
            return null;
        }
        public void ReceiveGoal(GroundedPredicate g)
        {
            if (tmpGoals.Contains(g))
            {
                tmpGoals.Remove(g);
            }
            allGoals.Add(g);
        }
        public void initPlaner()
        {
            foreach (GroundedPredicate gp in goal)
            {
                PublicPredicates.Add(gp);
                GroundedPredicate npg = (GroundedPredicate)gp.Negate();
                PublicPredicates.Add(npg);
            }
            TagPublicActions();

            FillFactDictionary(out allFactsWithActAchieve);
            canGetPredicate = new Dictionary<GroundedPredicate, List<Action>>();
            int j = 0;
            foreach (var act in privateActions)
            {
                act.index = j;
                j++;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (!canGetPredicate.ContainsKey(gp))
                    {
                        canGetPredicate.Add(gp, new List<Action>());
                    }
                    canGetPredicate[gp].Add(act);
                }
            }

            publicRelevantLandmark = publicLandmarks;
            //ReasonableOrdering = FindReasonableOrdering();
            //ReasonableOrdering = new List<Order>();
            bool[] landmarkVector = new bool[publicRelevantLandmark.Count];
            bool[] newLandmarkVector = new bool[publicRelevantLandmark.Count];
            indexOfGoals = new List<int>();

            for (int i = 0; i < landmarkVector.Length; i++)
            {
                landmarkVector[i] = false;
                if (publicRelevantLandmark[i].facts.ElementAt(0).Value.Equals("Goal"))
                {
                    indexOfGoals.Add(i);
                }
            }
            aproximationState = new State(startState);
            bool[] actionVector = new bool[privateActions.Count];
            UpdateAproximtState(aproximationState, actionVector);
            hashOfStates = new Dictionary<StateInfo, int>();
            mapToState = new Dictionary<int, StateInfo>();
            if (ReasonableOrdering == null)
                ReasonableOrdering = new List<Order>();
            bool[] reasonableOrdering = new bool[ReasonableOrdering.Count()];
            bool[] outReasonableOrdering = null;
            bool[] satisfiedNew = null;
            SatisfyLandmark(aproximationState.m_lPredicates, landmarkVector, out newLandmarkVector, reasonableOrdering, out outReasonableOrdering, out satisfiedNew);
            StateInfo firstStateInfo = new StateInfo(aproximationState, newLandmarkVector, actionVector, outReasonableOrdering, satisfiedNew);
            disTable = FindDisTable(startState);
            hashOfStates.Add(firstStateInfo, 0);
            mapToState.Add(0, firstStateInfo);
            initialVectors = new bool[2][];
            initialVectors[0] = newLandmarkVector;
            initialVectors[1] = outReasonableOrdering;
        }
        public void TagPublicActions()
        {
            foreach (Action act in m_actions)
            {
                bool f = false;
                bool f2 = false;
                if (publicActions.Contains(act))
                {
                    act.isPublic = true;
                    f2 = true;
                }

                foreach (GroundedPredicate eff in act.HashEffects)
                {
                    if (goal.Contains(eff))
                    {
                        //act.isPublic = true;
                        act.isGoalAction = true;
                        //break;
                    }
                    if (PublicPredicates.Contains(eff))
                    {
                        act.isPublic = true;
                        f = true;
                        // break;
                    }
                }
                if (!f2 && f)
                    publicActions.Add(act);
            }

        }
        public bool[][] GetInitialVectors()
        {
            publicRelevantLandmark = publicLandmarks;
            aproximationState = new State(startState);
            bool[] landmarkVector = new bool[publicRelevantLandmark.Count];
            bool[] newLandmarkVector = new bool[publicRelevantLandmark.Count];


            for (int i = 0; i < landmarkVector.Length; i++)
            {
                landmarkVector[i] = false;
            }
            bool[] actionVector = new bool[privateActions.Count];
            UpdateAproximtState(aproximationState, actionVector);

            bool[] reasonableOrdering = new bool[ReasonableOrdering.Count()];
            bool[] outReasonableOrdering = null;
            bool[] satisfiedNew = null;
            SatisfyLandmark(aproximationState.m_lPredicates, landmarkVector, out newLandmarkVector, reasonableOrdering, out outReasonableOrdering, out satisfiedNew);


            initialVectors = new bool[2][];
            initialVectors[0] = newLandmarkVector;
            initialVectors[1] = outReasonableOrdering;
            return initialVectors;
        }
        public void initPdbPlaner()
        {
            //publicRelevantLandmark = publicLandmarks;
            //ReasonableOrdering = FindReasonableOrdering();


            bool[] actionVector = new bool[privateActions.Count];
            Dictionary<GroundedPredicate, int> publicPredicateList = null;

            PdbUpdateAproximtState(aproximationState, actionVector, out publicPredicateList);
            //allStates = new List<StateInfo>();
            hashOfStates = new Dictionary<StateInfo, int>();
            mapToState = new Dictionary<int, StateInfo>();
            //SatisfyLandmark(aproximationState.m_lPredicates, landmarkVector, out newLandmarkVector, reasonableOrdering, out outReasonableOrdering);
            StateInfo firstStateInfo = new StateInfo(aproximationState, actionVector, publicPredicateList);
            //disTable = FindDisTable(startState);
            hashOfStates.Add(firstStateInfo, 0);
            mapToState.Add(0, firstStateInfo);
            canGetPredicate = new Dictionary<GroundedPredicate, List<Action>>();
            int i = 0;
            foreach (var act in privateActions)
            {
                act.index = i;
                i++;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (!canGetPredicate.ContainsKey(gp))
                    {
                        canGetPredicate.Add(gp, new List<Action>());
                    }
                    canGetPredicate[gp].Add(act);
                }
            }


        }
        public List<GroundedPredicate> InitBackwardHspGraph()
        {
            currentLayer = new HashSet<GroundedPredicate>();
            predicateGrade = new Dictionary<GroundedPredicate, int>();
            List<GroundedPredicate> publish = new List<GroundedPredicate>();
            level=0;
            foreach (GroundedPredicate gp in goal)
            {
                predicateGrade.Add(gp, level);
                currentLayer.Add(gp);
                if (PublicPredicates.Contains(gp))
                {
                    publish.Add(gp);
                }
            }
            return publish;
        }
        public List<GroundedPredicate> UpdateBackwardHspGraph(List<GroundedPredicate> othersPublic,out bool change)
        {
            level=level+1;
            HashSet<GroundedPredicate> nextCurrentLayer = new HashSet<GroundedPredicate>();
            List<GroundedPredicate> publish = new List<GroundedPredicate>();
            change = false;
            foreach (GroundedPredicate pGp in othersPublic)
            {
                currentLayer.Add(pGp);
            }
            foreach (Action act in m_actions)
            {
                bool flag = false;
                foreach (GroundedPredicate eff in act.HashEffects)
                {
                    if (currentLayer.Contains(eff))
                    {
                        flag = true;
                        break;
                    }
                }
                if (flag)
                {
                    foreach (GroundedPredicate pre in act.HashPrecondition)
                    {
                        if (!predicateGrade.ContainsKey(pre))
                        {
                            change = true;
                            predicateGrade.Add(pre, level);
                            nextCurrentLayer.Add(pre);
                            if (PublicPredicates.Contains(pre))
                            {
                                publish.Add(pre);
                            }
                        }
                    }
                }
            }
            currentLayer = nextCurrentLayer;
            return publish;
        }
        public void PdbUpdateAproximtState(State s, bool[] actionsVector, out Dictionary<GroundedPredicate, int> publicPre)
        {
            publicPre = new Dictionary<GroundedPredicate, int>();
            HashSet<Action> allReadyUse = new HashSet<Action>();
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;

                int i = 0;
                foreach (Action act in privateActions)
                {
                    if (allReadyUse.Contains(act))
                         continue;

                    if (actionsVector[i] == false)
                    {
                        if (Contains(s, act.HashPrecondition))
                        {
                            allReadyUse.Add(act);
                            actionsVector[i] = true;
                            if (act.Effects != null)
                            {
                                foreach (GroundedPredicate addProp in act.HashEffects)
                                {
                                    if (!s.Predicates.Contains(addProp))
                                    {
                                        s.AddPredicate(addProp);
                                        flag2 = true;
                                    }

                                }
                            }

                        }
                    }
                    allReadyUse.Add(act);
                    i++;
                }



            }
            foreach (GroundedPredicate gp in s.m_lPredicates)
            {
                if (PublicPredicates.Contains(gp))
                    publicPre.Add(gp, 0);
            }
            try
            {
                State tmpState = new State(s);
                bool stop = false;
                int level = 1;
                List<GroundedPredicate> setCopy = new List<GroundedPredicate>();
                while (!stop)
                {
                    stop = true;
                    foreach (Action action in m_actions)
                    {
                        if (allReadyUse.Contains(action))
                            continue;
                        if (Contains(tmpState, action.HashPrecondition))
                        {
                            allReadyUse.Add(action);
                            foreach (GroundedPredicate eff in action.HashEffects)
                            {
                                if (!tmpState.m_lPredicates.Contains(eff) && !setCopy.Contains(eff))
                                {
                                    //publicPre.Add(eff, 1);
                                    setCopy.Add(eff);
                                }
                            }
                        }
                    }
                    foreach (GroundedPredicate add in setCopy)
                    {
                        tmpState.m_lPredicates.Add(add);
                        if (PublicPredicates.Contains(add))
                        {
                            publicPre.Add(add, level);
                        }
                        stop = false;
                    }
                    level++;
                    setCopy = new List<GroundedPredicate>();
                }

            }
            catch (Exception ex)
            {
                Console.Write("*");
            }

        }
        private bool Contains(HashSet<Predicate> x, List<Predicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }

        public int EvalueteState(int stateNumber,HashSet<GroundedPredicate> publics)
        {
            StateInfo oldState = mapToState[stateNumber];
            int sum = 0;
            int count = 0;
            int max = 0;
            foreach (GroundedPredicate fact in oldState.state.m_lPredicates)
            {
                if (predicateGrade.ContainsKey(fact) && !publics.Contains(fact))
                {
                    sum += predicateGrade[fact];
                    count++;
                    if (max < predicateGrade[fact])
                        max = predicateGrade[fact];
                    if(PublicPredicates.Contains(fact))
                    {
                        publics.Add(fact);
                    }
                }
            }
            return sum / count;
        }

        public KeyValuePair<int, double> PdbDemoApply(int stateNumber, string agentName, CompoundFormula agentEff, List<Predicate> preCon,Action act)
        {
            if (agentName == name)
            {

               // StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key; ;
                StateInfo oldState = mapToState[stateNumber]; 
                bool[] newActionsVector = new bool[privateActions.Count];
                for (int i = 0; i < oldState.actionVector.Length; i++)
                {
                    newActionsVector[i] =  oldState.actionVector[i];////
                }
                State newState = oldState.state.ApplyFormulaEffectII(agentEff, MutuallyExclusive, PublicPredicates, canGetPredicate, newActionsVector, publicActions, preCon);
               // newState = oldState.state.ApplyEffectCf(act, MutuallyExclusive, act.HashPrecondition, PublicPredicates, canGetPredicate, newActionsVector, privateActions);
                


                if (newState == null)
                    return new KeyValuePair<int, double>(-1, -1);

                Dictionary<GroundedPredicate, int> publicPre = null;

                PdbUpdateAproximtState(newState, newActionsVector, out publicPre);




                StateInfo state = new StateInfo(newState, newActionsVector, publicPre);
                int stateIndex = -1;
                if (!hashOfStates.ContainsKey(state))
                {
                    hashOfStates.Add(state, hashOfStates.Count);
                    mapToState.Add(hashOfStates.Count-1, state);
                    stateIndex = hashOfStates.Count - 1;
                }
                else
                {
                    stateIndex = hashOfStates[state];
                }

                return new KeyValuePair<int, double>(stateIndex, 0);
            }
            else
            {

                //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key; ;
                StateInfo oldState = mapToState[stateNumber]; 
                bool[] newActionsVector = new bool[privateActions.Count];
                for (int i = 0; i < oldState.actionVector.Length; i++)
                {
                    newActionsVector[i] = oldState.actionVector[i];////
                }
                Dictionary<GroundedPredicate, int> publicPre = new Dictionary<GroundedPredicate, int>(oldState.publicPredicate);
                State newState = oldState.state.PassiveApplyFormulaEffect(agentEff, MutuallyExclusive, PublicPredicates, canGetPredicate, newActionsVector, privateActions, publicPre);
                bool relevantToMe = false;
                foreach(GroundedPredicate gp in act.HashEffects)
                {
                    //if (PublicPredicates.Contains(gp) || PublicPredicates.Contains((GroundedPredicate)gp.Negate()))
                    if (PublicPredicates.Contains(gp))
                        relevantToMe = true;
                }
                StateInfo state = null;
                if (relevantToMe)
                {
                    PdbUpdateAproximtState(newState, newActionsVector, out publicPre);
                    state = new StateInfo(newState, newActionsVector, publicPre);
                }
                else
                {
                    state = new StateInfo(newState, oldState.actionVector, oldState.publicPredicate);
                }
                int stateIndex = -1;
                if (!hashOfStates.ContainsKey(state))
                {
                    hashOfStates.Add(state, hashOfStates.Count);
                    mapToState.Add(hashOfStates.Count-1, state);
                    stateIndex = hashOfStates.Count - 1;
                }
                else
                {
                    stateIndex = hashOfStates[state];
                }
                return new KeyValuePair<int, double>(stateIndex, 0);



            }
        }
        public HashSet<GroundedPredicate> GetAllPublicPreconditions()
        {
            HashSet<GroundedPredicate> ans = new HashSet<GroundedPredicate>();

            foreach (Action act in publicActions)
            {
                foreach (GroundedPredicate gp in act.HashPrecondition)
                {
                    if (PublicPredicates.Contains(gp))
                    {
                        ans.Add(gp);
                    }
                }
            }
            return ans;
        }
        public HashSet<GroundedPredicate> GetAllPublicEffects()
        {
            HashSet<GroundedPredicate> ans = new HashSet<GroundedPredicate>();
            foreach (Action act in publicActions)
            {
                foreach (GroundedPredicate gp in act.HashPrecondition)
                {
                    if (PublicPredicates.Contains(gp))
                    {
                        ans.Add(gp);
                    }
                }
            }
            return ans;
        }
        public void initLandmarksDetect()
        {
            WhatICanGetWithMyPrivate();
        }
        public void initPublicLandmarksDetect(Landmark l)
        {
            localDiscoverdLandmark = new List<Landmark>();
            if (l != null)
                localDiscoverdLandmark.Add(l);

        }
        public void ChangeInitialState(int stateNumber)
        {
           // StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;
            StateInfo oldState = mapToState[stateNumber]; 
            startState = oldState.state;
            WhatICanGetWithMyPrivate();
        }

        public void BackToOrginalInitialState()
        {
           // startState = orginalStartState;
        }

        public int ResetStateInfo(int stateNumber)
        {
            try
            {
               // StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;
                StateInfo oldState = mapToState[stateNumber]; 
                mapToState.Remove(stateNumber);
                hashOfStates.Remove(oldState);
                
                publicRelevantLandmark = publicLandmarks;
                //ReasonableOrdering = FindReasonableOrdering();
                //ReasonableOrdering = new List<Order>();
                bool[] landmarkVector = new bool[publicRelevantLandmark.Count];
                bool[] newLandmarkVector = new bool[publicRelevantLandmark.Count];
                indexOfGoals = new List<int>();

                for (int i = 0; i < landmarkVector.Length; i++)
                {
                    landmarkVector[i] = false;
                    if (publicRelevantLandmark[i].facts.ElementAt(0).Value.Equals("Goal"))
                    {
                        indexOfGoals.Add(i);
                    }
                }
                bool[] actionVector = new bool[privateActions.Count];
                //UpdateAproximtState(aproximationState, actionVector);

                bool[] reasonableOrdering = new bool[ReasonableOrdering.Count()];
                bool[] outReasonableOrdering = null;
                bool[] satisfiedNew = null;
                SatisfyLandmark(oldState.state.m_lPredicates, landmarkVector, out newLandmarkVector, reasonableOrdering, out outReasonableOrdering, out satisfiedNew);
                StateInfo firstStateInfo = new StateInfo(oldState.state, newLandmarkVector, actionVector, outReasonableOrdering, satisfiedNew);
                disTable = FindDisTable(startState);
                //int p = hashOfStates[firstStateInfo];
                //hashOfStates.Add(firstStateInfo, hashOfStates.Count);
                hashOfStates = new Dictionary<StateInfo, int>();
                hashOfStates.Add(firstStateInfo, hashOfStates.Count);
                mapToState.Add(hashOfStates.Count, firstStateInfo);
            }
            catch (Exception ex)
            {
                throw new NotImplementedException();
            }
            return hashOfStates.Count - 1;
        }
        public List<Landmark> GetPublicAndArtificialGoal()
        {
            List<Landmark> lgoals = new List<Landmark>();
            foreach (GroundedPredicate gp in goal)
            {
                if (PublicPredicates.Contains(gp))
                {
                    Landmark l = new Landmark("Goal", true);
                    gp.isPublic = true;
                    l.AddPublicFact(gp, "goal");
                    lgoals.Add(l);
                }
                else
                {
                    List<Landmark> artificialGoals = Distributed_Landmarks_Detection.GetPublicLandmarks(gp, this);
                    lgoals.AddRange(artificialGoals);
                }
            }
            return lgoals;
        }
        public List<Order> FindReasonableOrdering(List<Landmark> relevantLandmarks, List<Order> necessaryOrders, List<Agent> agents)
        {
            orderList = necessaryOrders;
            publicRelevantLandmark = relevantLandmarks;
            publicLandmarks = relevantLandmarks;
            ReasonableOrdering = FindReasonableOrdering(agents);
            return ReasonableOrdering;
        }
        public void SetReasonableOrdering(List<Order> m_ReasonableOrdering)
        {
            ReasonableOrdering = m_ReasonableOrdering;
        }
        public void ReducePublicActions(Dictionary<string, HashSet<GroundedPredicate>> agentsPublicFacts)
        {
            List<Action> delActions = new List<Action>();
            HashSet<GroundedPredicate> RelevantPublicFacts = new HashSet<GroundedPredicate>();
            foreach (Action publicAct in publicActions)
            {
                bool isPrivate = true;
                foreach (GroundedPredicate pre in publicAct.HashPrecondition)
                {

                    foreach (var agentPublicFacts in agentsPublicFacts)
                    {
                        if (agentPublicFacts.Key.Equals(name))
                            continue;
                        if (agentPublicFacts.Value.Contains(pre) || agentPublicFacts.Value.Contains((GroundedPredicate)pre.Negate()))
                        {
                            isPrivate = false;
                            break;
                        }
                    }
                    if (!isPrivate)
                        break;
                }
                if (isPrivate)
                {
                    foreach (GroundedPredicate eff in publicAct.HashEffects)
                    {

                        foreach (var agentPublicFacts in agentsPublicFacts)
                        {
                            if (agentPublicFacts.Key.Equals(name))
                                continue;
                            if (agentPublicFacts.Value.Contains(eff) || agentPublicFacts.Value.Contains((GroundedPredicate)eff.Negate()))
                            {
                                isPrivate = false;
                                break;
                            }
                        }
                        if (!isPrivate)
                            break;
                    }
                }
                if (isPrivate)
                {
                    delActions.Add(publicAct);
                }
            }
            foreach (Action act in delActions)
            {
                publicActions.Remove(act);
                privateActions.Add(act);
                foreach (GroundedPredicate pre in act.HashPrecondition)
                {
                    PublicPredicates.Remove(pre);
                    PublicPredicates.Remove((GroundedPredicate)pre.Negate());
                }
                foreach (GroundedPredicate eff in act.HashEffects)
                {
                    PublicPredicates.Remove(eff);
                    PublicPredicates.Remove((GroundedPredicate)eff.Negate());
                }
            }
            foreach (Action publicAct in publicActions)
            {
                foreach (GroundedPredicate pre in publicAct.HashPrecondition)
                {
                    if (PublicPredicates.Contains(pre))
                    {
                        RelevantPublicFacts.Add(pre);
                    }
                }

                foreach (GroundedPredicate eff in publicAct.HashEffects)
                {
                    if (PublicPredicates.Contains(eff))
                    {
                        RelevantPublicFacts.Add(eff);
                    }
                }
            }
            
            PublicPredicates = RelevantPublicFacts;
        }
        private Dictionary<GroundedPredicate, int> FindDisTable(State state)
        {
            Dictionary<GroundedPredicate, int> ans = new Dictionary<GroundedPredicate, int>();
            HashSet<Action> actions = new HashSet<Action>();

            /*foreach (Action act in m_actions)
            {

                {
                    actions.Add(act);
                }
            }*/
            foreach (Action act in allActionsWithProjectionAction)
            {

                {
                    actions.Add(act);
                }
            }

            HashSet<GroundedPredicate> s = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in state.Predicates)
            {
                ans.Add(gp, 0);
                s.Add(gp);
            }

            bool flag = true;
            int level = 0;
            while (flag)
            {
                flag = false;
                HashSet<GroundedPredicate> tmp = new HashSet<GroundedPredicate>();
                List<Action> dell = new List<Action>();
                foreach (Action act in actions)
                {

                    if (Contains(s, act.HashPrecondition))
                    {
                        foreach (GroundedPredicate gp in act.HashEffects)
                        {
                            if (!s.Contains(gp) && !tmp.Contains(gp))
                            {

                                tmp.Add(gp);
                                flag = true;

                            }

                        }
                        dell.Add(act);
                    }




                }
                level++;

                foreach (GroundedPredicate gp in tmp)
                {
                    s.Add(gp);
                    ans.Add(gp, level);
                }
                foreach (Action dellact in dell)
                {
                    actions.Remove(dellact);
                }
            }

            cantDonePrivateAction = actions.ToList();
            return ans;

        }
        public int CantReachTheGoal(int stateIndex)
        {

            // if (publicRelevantLandmark.Count > 0) return false;
            int count = 0;
            //StateInfo curentState = hashOfStates.ElementAt(stateIndex).Key;
            StateInfo curentState = mapToState[stateIndex]; 
            //HashSet<Predicate> gpSet = new HashSet<Predicate>(curentState.state.m_lPredicates);
            // bool flag=true;
            /* while (flag)
             {
                 flag = false;
                 foreach (Action act in privateActions)
                 {
                     if(Contains(gpSet,act.HashPrecondition))
                     {
                         foreach(var v in act.HashEffects)
                         {
                             if(!gpSet.Contains(v))
                             {
                                 flag = true;
                                 gpSet.Add(v);
                             }
                         }
                     }
                 }
             }*/
            foreach (GroundedPredicate gp in goal)
            {
                if (!PublicPredicates.Contains(gp) && !curentState.state.m_lPredicates.Contains(gp))
                {
                    count++; ;
                }
            }

            return count;

        }
        public int h(PatternDatabase pdb, Landmark l, int stateNumber)
        {
            //StateInfo state = hashOfStates.ElementAt(stateNumber).Key;
            StateInfo state = mapToState[stateNumber];
            Dictionary<GroundedPredicate, int> temporalRelaxCost = state.publicPredicate;
            Dictionary<GroundedPredicate, int> predicateCost = new Dictionary<GroundedPredicate, int>();



            int cost = 1000;//-1;
            foreach (GroundedPredicate gp in l.facts.Keys)
            {
                if (pdb.cooperationCanGet.ContainsKey(gp))
                {
                    foreach (var kvp in pdb.cooperationCanGet[gp])
                    {
                        if (temporalRelaxCost.ContainsKey(kvp.Key) && (temporalRelaxCost[kvp.Key] + kvp.Value) < cost)
                        {
                            cost = (temporalRelaxCost[kvp.Key] + kvp.Value);
                        }
                    }
                }

            }
            //if (cost == 1000)
            //    Console.WriteLine("*");
            //if (cost > -1)
            return cost;
            // else
            //    return
            //       1000;
        }
        private int FindDis(Action act)
        {
            if (act.Preconditions == null)
                return 0;
            int sum = 0;
            foreach (GroundedPredicate gp in act.HashPrecondition)
            {
                if (!disTable.ContainsKey(gp))
                    return -1;

                sum += disTable[gp];
            }
            return sum;
        }
        public List<GroundedPredicate> GetPublicInitial()
        {
            List<GroundedPredicate> state = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in startState.Predicates)
            {
                if (PublicPredicates.Contains(gp))
                {
                    state.Add(gp);
                }
            }
            return state;
        }
        public HashSet<GroundedPredicate> GetPublicStartState()
        {
            HashSet<GroundedPredicate> state = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in startState.Predicates)
            {
                if (PublicPredicates.Contains(gp))
                {
                    state.Add(gp);
                }
            }
            foreach (KeyValuePair<GroundedPredicate,GroundedPredicate> mapFactToArtifitial in mapGpToArtificial)
            {
                if (privateCanGet.Contains(mapFactToArtifitial.Key))
                {
                       state.Add(mapFactToArtifitial.Value);                   
                }
            }
            return state;
        }
        public HashSet<GroundedPredicate> GetPublicStartState2(Dictionary<string,Action> projActions)
        {

            HashSet<GroundedPredicate> state = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in startState.Predicates)
            {
                if (PublicPredicates.Contains(gp))
                {
                    state.Add(gp);
                }
            }
            foreach (Action act in publicActions)
            {
                if (Contains(privateCanGet, act.HashPrecondition))
                {
                    foreach (GroundedPredicate gp in projActions[act.Name].HashPrecondition)
                    {
                        state.Add(gp);
                    }
                }
            }
            return state;
        }
        public HashSet<Predicate> GetPublicStartState(HashSet<Predicate> courrentState, HashSet<Predicate> privateCanGet)
        {
            HashSet<Predicate> state = new HashSet<Predicate>();
            foreach (GroundedPredicate gp in courrentState)
            {
                if (PublicPredicates.Contains(gp))
                {
                    state.Add(gp);
                }
            }
        
            foreach (KeyValuePair<GroundedPredicate, GroundedPredicate> mapFactToArtifitial in mapGpToArtificial)
            {
                if (privateCanGet.Contains(mapFactToArtifitial.Key))
                {
                      state.Add(mapFactToArtifitial.Value);  
                }
            }
            return state;
        }
        public List<GroundedPredicate> GetPrivateStartState()
        {
            List<GroundedPredicate> state = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in startState.Predicates)
            {
                if (!PublicPredicates.Contains(gp))
                {
                    state.Add(gp);
                }
            }
            return state;
        }
        Dictionary<string, Dictionary<string,HashSet<Action>>> mapActToList = null;
        Dictionary<string, HashSet<Action>> mapActToListForDelete = null;
        
        Dictionary<GroundedPredicate, HashSet<Action>> mapAGpToList = null;
        public List<Action> getAdvancedProjectionPublicAction(int index, List<Predicate> newPredicates)
        {
            mapActToList = new Dictionary<string, Dictionary<string, HashSet<Action>>>();
            mapAGpToList = new Dictionary<GroundedPredicate, HashSet<Action>>();
            Dictionary<string, Action> mapActionName = new Dictionary<string, Action>();

            mapGpToArtificial = new Dictionary<GroundedPredicate, GroundedPredicate>();


            ArtificialToPrivate = new Dictionary<GroundedPredicate, GroundedPredicate>();
            Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> mapGpToArtlGp = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            foreach (Action act in publicActions)
            {
                Action newAction = new Action(act.Name);
                newAction.Preconditions = act.Preconditions;
                newAction.Effects = act.Effects;
                newAction.LoadPrecondition();

                mapActionName[act.Name] = newAction;

            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree = 0;

                CompoundFormula pre = new CompoundFormula("and");
                int globaDepth = 0;
                foreach (GroundedPredicate gpPre in act.Preconditions.GetAllPredicates())
                {
                    string gpName = gpPre.Name + gpPre.Constants[0];
                    if (gpPre.Name.Contains(Domain.ARTIFICIAL_PREDICATE) || PublicPredicates.Contains(gpPre))
                    {
                        pre.AddOperand(gpPre);
                    }
                    else
                    {
                        if (!mapGpToArtificial.ContainsKey(gpPre))
                        {


                            int depth1;
                            int depth2;
                            int tmp = AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree;
                            HashSet<Action> Achievers = Distributed_Landmarks_Detection.GetPublicActionsLandmarks2(gpPre, this, out depth1, true);
                            if (Achievers.Count > 0)
                            {
                                if (mapActToList.ContainsKey(act.Name))
                                {
                                    mapActToList[act.Name].Add(gpName, Achievers);
                                    /*var firstList = mapActToList[act.Name];
                                    mapActToList[act.Name] = new HashSet<Action>();
                                    foreach (Action sAct in Achievers)
                                    {
                                        if (firstList.Contains(sAct))
                                            mapActToList[act.Name].Add(sAct);
                                    }*/

                                }
                                else
                                {
                                    mapActToList.Add(act.Name, new Dictionary<string, HashSet<Action>>());
                                    mapActToList[act.Name].Add(gpName, Achievers);
                                }
                                mapAGpToList.Add(gpPre, Achievers);
                            }

                            int i = 0;
                            int tmpCounter = 1;
                            i++;
                            GroundedPredicate newPrePredicate = null;
                            newPrePredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + index);
                            mapGpToArtificial[gpPre] = newPrePredicate;
                            ArtificialToPrivate[newPrePredicate] = gpPre;
                            newPredicates.Add(newPrePredicate);
                            newPredicates.Add((GroundedPredicate)newPrePredicate.Negate());

                            index++;
                            pre.AddOperand(newPrePredicate);
                            foreach (Action achiever in Achievers)
                            {
                                CompoundFormula cf = new CompoundFormula("and");
                                cf.AddOperand(mapActionName[achiever.Name].Effects);
                                cf.AddOperand(newPrePredicate);
                                mapActionName[achiever.Name].Effects = cf;
                                mapActionName[achiever.Name].LoadPrecondition();
                                if (mapActionName[achiever.Name].mapEff == null)
                                    mapActionName[achiever.Name].mapEff = new Dictionary<string, HashSet<GroundedPredicate>>();

                                if (!mapActionName[achiever.Name].mapEff.ContainsKey(gpName))
                                    mapActionName[achiever.Name].mapEff.Add(gpName, new HashSet<GroundedPredicate>());
                                mapActionName[achiever.Name].mapEff[gpName].Add(newPrePredicate);

                            }


                        }
                        else
                        {
                            pre.AddOperand(mapGpToArtificial[gpPre]);
                            if (mapAGpToList.ContainsKey(gpPre))
                            {
                                if (mapActToList.ContainsKey(act.Name))
                                {
                                    mapActToList[act.Name].Add(gpName, mapAGpToList[gpPre]);
                                    /* var firstList = mapActToList[act.Name];
                                     mapActToList[act.Name] = new HashSet<Action>();
                                     foreach (Action sAct in mapAGpToList[gpPre])
                                     {
                                         if (firstList.Contains(sAct))
                                             mapActToList[act.Name].Add(sAct);
                                     }*/
                                }
                                else
                                {
                                    mapActToList.Add(act.Name, new Dictionary<string, HashSet<Action>>());
                                    mapActToList[act.Name].Add(gpName, mapAGpToList[gpPre]);
                                }
                            }
                        }

                    }
                }
                if (mapActionName.ContainsKey(actionName))
                {
                    mapActionName[actionName].Preconditions = pre;
                    mapActionName[actionName].LoadPrecondition();
                }
                else
                {
                    Console.WriteLine("*");
                }
            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                HashSet<Predicate> hash = new HashSet<Predicate>();
                CompoundFormula eff = new CompoundFormula("and");
                foreach (GroundedPredicate gpEff in act.Effects.GetAllPredicates())
                {
                    if (PublicPredicates.Contains(gpEff) || gpEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                    {
                        eff.AddOperand(gpEff);
                        hash.Add(gpEff);
                    }
                    else
                    {
                      //  continue;
                        if (gpEff.Negation)// && act.HashPrecondition.Contains(gpEff.Negate()))
                        {
                            string gpName = gpEff.Name + gpEff.Constants[0];
                            GroundedPredicate gp = (GroundedPredicate)gpEff.Negate();
                            string ngpName = gp.Name + gp.Constants[0];
                            if (mapActToList.ContainsKey(act.Name) && mapActToList[act.Name].ContainsKey(ngpName))
                            {
                                foreach (Action actName in mapActToList[act.Name][ngpName])
                                {
                                    Action preAction = mapActionName[actName.Name];
                                    if (preAction.mapEff.ContainsKey(ngpName))
                                    {
                                        foreach (GroundedPredicate preEff in preAction.mapEff[ngpName])
                                        {
                                            if (!preEff.Negation)
                                            {
                                                if (preEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                                                {
                                                    if (!hash.Contains(preEff.Negate()))
                                                    {
                                                        eff.AddOperand(preEff.Negate());
                                                        hash.Add(preEff.Negate());
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                             if (mapGpToArtificial.ContainsKey(gp))
                             {
                                 if (!hash.Contains(mapGpToArtificial[gp].Negate()))
                                 {
                                     Predicate ngp = mapGpToArtificial[gp].Negate();
                                     eff.AddOperand(ngp);
                                     hash.Add(ngp);
                                 }
                             }
                        }
                    }
                }
                mapActionName[actionName].Effects = eff;
                mapActionName[actionName].LoadPrecondition();
            }
            return mapActionName.Values.ToList();
        }
        public List<Action> getAdvancedProjectionPublicAction2(int index, List<Predicate> newPredicates, State s)
        {
            Dictionary<string, HashSet<Action>> mapActToList = new Dictionary<string, HashSet<Action>>();
            mapAGpToList = new Dictionary<GroundedPredicate, HashSet<Action>>();
            Dictionary<string, Action> mapActionName = new Dictionary<string, Action>();

            mapGpToArtificial = new Dictionary<GroundedPredicate, GroundedPredicate>();


            ArtificialToPrivate = new Dictionary<GroundedPredicate, GroundedPredicate>();
            Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> mapGpToArtlGp = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            foreach (Action act in publicActions)
            {
                Action newAction = new Action(act.Name);
                newAction.Preconditions = act.Preconditions;
                newAction.Effects = act.Effects;
                newAction.LoadPrecondition();

                mapActionName[act.Name] = newAction;

            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree = 0;

                CompoundFormula pre = new CompoundFormula("and");
                int globaDepth = 0;
                foreach (GroundedPredicate gpPre in act.Preconditions.GetAllPredicates())
                {
                    if (gpPre.Name.Contains(Domain.ARTIFICIAL_PREDICATE) || PublicPredicates.Contains(gpPre))
                    {
                        pre.AddOperand(gpPre);
                    }
                    else
                    {
                        if (!mapGpToArtificial.ContainsKey(gpPre))
                        {


                            int depth1;
                            int depth2;
                            int tmp = AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree;
                            HashSet<Action> Achievers = Distributed_Landmarks_Detection.GetPublicActionsLandmarks2(gpPre, this, out depth1, true);
                            

                            int i = 0;
                            int tmpCounter = 1;
                            i++;
                            GroundedPredicate newPrePredicate = null;
                            newPrePredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + index);
                            mapGpToArtificial[gpPre] = newPrePredicate;
                            ArtificialToPrivate[newPrePredicate] = gpPre;
                            newPredicates.Add(newPrePredicate);
                            newPredicates.Add((GroundedPredicate)newPrePredicate.Negate());

                            index++;
                            pre.AddOperand(newPrePredicate);
                            foreach (Action achiever in Achievers)
                            {
                                CompoundFormula cf = new CompoundFormula("and");
                                cf.AddOperand(mapActionName[achiever.Name].Effects);
                                cf.AddOperand(newPrePredicate);
                                mapActionName[achiever.Name].Effects = cf;
                                mapActionName[achiever.Name].LoadPrecondition();
                            }
                            if(!mapGpToArtlGp.ContainsKey(gpPre))
                            {
                                mapGpToArtlGp.Add(gpPre, new HashSet<GroundedPredicate>());
                            }
                            mapGpToArtlGp[gpPre].Add(newPrePredicate);

                        }
                        else
                        {
                            pre.AddOperand(mapGpToArtificial[gpPre]);
                            if (mapAGpToList.ContainsKey(gpPre))
                            {
                                if (mapActToList.ContainsKey(act.Name))
                                {
                                    // mapActToList[act.Name].UnionWith(mapAGpToList[gpPre]);

                                    var firstList = mapActToList[act.Name];
                                    mapActToList[act.Name] = new HashSet<Action>();
                                    foreach (Action sAct in mapAGpToList[gpPre])
                                    {
                                        if (firstList.Contains(sAct))
                                            mapActToList[act.Name].Add(sAct);
                                    }
                                }
                                else
                                {
                                    mapActToList.Add(act.Name, mapAGpToList[gpPre]);
                                }
                            }
                        }

                    }
                }
                if (mapActionName.ContainsKey(actionName))
                {
                    mapActionName[actionName].Preconditions = pre;
                    mapActionName[actionName].LoadPrecondition();
                }
                else
                {
                    Console.WriteLine("*");
                }
            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                HashSet<Predicate> hash = new HashSet<Predicate>();
                CompoundFormula eff = new CompoundFormula("and");
                foreach (GroundedPredicate gpEff in act.Effects.GetAllPredicates())
                {
                    if (PublicPredicates.Contains(gpEff) || gpEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                    {
                        eff.AddOperand(gpEff);
                        hash.Add(gpEff);
                    }
                    else
                    {
                        if (gpEff.Negation)
                        {
                            GroundedPredicate gp = (GroundedPredicate)gpEff.Negate();


                            foreach (Action actName in mapActToList[act.Name])
                            {
                                Action preAction = mapActionName[actName.Name];
                                foreach (GroundedPredicate preEff in preAction.Effects.GetAllPredicates())
                                {
                                    if (!preEff.Negation)
                                    {
                                        if (preEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                                        {
                                            if (!hash.Contains(preEff.Negate()))
                                            {
                                                eff.AddOperand(preEff.Negate());
                                                hash.Add(preEff.Negate());
                                            }
                                        }
                                    }
                                }
                            }
                            if (mapGpToArtificial.ContainsKey(gp))
                            {
                                if (!hash.Contains(mapGpToArtificial[gp].Negate()))
                                {
                                    Predicate ngp = mapGpToArtificial[gp].Negate();
                                    eff.AddOperand(ngp);
                                    hash.Add(ngp);
                                }
                            }
                        }
                    }
                }
                mapActionName[actionName].Effects = eff;
                mapActionName[actionName].LoadPrecondition();
            }
            return mapActionName.Values.ToList();
        }
        public Dictionary<string, Action> getAdvancedProjectionPublicAction3(int index, List<Predicate> newPredicates, State s)
        {
            Dictionary<string, HashSet<Action>> mapActToList = new Dictionary<string, HashSet<Action>>();
            mapActToListForDelete = new Dictionary<string, HashSet<Action>>();
            mapAGpToList = new Dictionary<GroundedPredicate, HashSet<Action>>();
            Dictionary<string, Action> mapActionName = new Dictionary<string, Action>();

            mapGpToArtificial = new Dictionary<GroundedPredicate, GroundedPredicate>();


            ArtificialToPrivate = new Dictionary<GroundedPredicate, GroundedPredicate>();

            foreach (Action act in publicActions)
            {
                Action newAction = new Action(act.Name);
                newAction.Preconditions = act.Preconditions;
                newAction.Effects = act.Effects;
                newAction.LoadPrecondition();

                mapActionName[act.Name] = newAction;

            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree = 0;

                CompoundFormula pre = new CompoundFormula("and");
                int globaDepth = 0;
                foreach (GroundedPredicate gpPre in act.Preconditions.GetAllPredicates())
                {
                    if (gpPre.Name.Contains(Domain.ARTIFICIAL_PREDICATE) || PublicPredicates.Contains(gpPre))
                    {
                        pre.AddOperand(gpPre);
                    }
                    else
                    {
                        if (!mapGpToArtificial.ContainsKey(gpPre))
                        {


                            int depth1;
                            int depth2;
                            int tmp = AdvancedLandmarkProjectionPlaner.sizeOfRegressionTree;
                            HashSet<Action> Achievers = Distributed_Landmarks_Detection.GetPublicActionsLandmarks2(gpPre, this, out depth1, true);
                            if (Achievers.Count > 0)
                            {
                                if (mapActToList.ContainsKey(act.Name))
                                {
                                    mapActToListForDelete[act.Name].UnionWith(Achievers);
                                    // mapActToList[act.Name].UnionWith(Achievers);
                                    var firstList = mapActToList[act.Name];
                                    mapActToList[act.Name] = new HashSet<Action>();
                                    foreach (Action sAct in Achievers)
                                    {
                                        if (firstList.Contains(sAct))
                                            mapActToList[act.Name].Add(sAct);
                                    }

                                }
                                else
                                {
                                    mapActToListForDelete.Add(act.Name,new HashSet<Action>(Achievers));
                                    mapActToList.Add(act.Name, Achievers);
                                }

                            }                        
                        }
                        else
                        {
                            if (mapAGpToList.ContainsKey(gpPre))
                            {
                                if (mapActToList.ContainsKey(act.Name))
                                {
                                    // mapActToList[act.Name].UnionWith(mapAGpToList[gpPre]);
                                    mapActToListForDelete[act.Name].UnionWith(mapAGpToList[gpPre]);

                                    var firstList = mapActToList[act.Name];
                                    mapActToList[act.Name] = new HashSet<Action>();
                                    foreach (Action sAct in mapAGpToList[gpPre])
                                    {
                                        if (firstList.Contains(sAct))
                                            mapActToList[act.Name].Add(sAct);
                                    }
                                }
                                else
                                {
                                    mapActToListForDelete.Add(act.Name, new HashSet<Action>(mapAGpToList[gpPre]));
                                    mapActToList.Add(act.Name, mapAGpToList[gpPre]);
                                }
                            }
                        }

                    }
                }
                if (mapActionName.ContainsKey(actionName))
                {
                    mapActionName[actionName].Preconditions = pre;
                    mapActionName[actionName].LoadPrecondition();
                }
                else
                {
                    Console.WriteLine("*");
                }
            }
            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                CompoundFormula pre = (CompoundFormula)act.Preconditions;
                GroundedPredicate newPrePredicate = null;
                newPrePredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + index);
                newPredicates.Add(newPrePredicate);
                newPredicates.Add((GroundedPredicate)newPrePredicate.Negate());

                index++;
                pre.AddOperand(newPrePredicate);
                foreach (Action achiever in mapActToList[actionName])
                {
                    CompoundFormula cf = new CompoundFormula("and");
                    cf.AddOperand(mapActionName[achiever.Name].Effects);
                    cf.AddOperand(newPrePredicate);
                    mapActionName[achiever.Name].Effects = cf;
                    mapActionName[achiever.Name].LoadPrecondition();
                }
            }


            foreach (var actionName in mapActionName.Keys.ToList())
            {
                Action act = mapActionName[actionName];
                HashSet<Predicate> hash = new HashSet<Predicate>();
                CompoundFormula eff = new CompoundFormula("and");
                foreach (GroundedPredicate gpEff in act.Effects.GetAllPredicates())
                {
                    if (PublicPredicates.Contains(gpEff) || gpEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                    {
                        eff.AddOperand(gpEff);
                        hash.Add(gpEff);
                    }
                }
                foreach (GroundedPredicate gpEff in act.Effects.GetAllPredicates())
                {

                    if (gpEff.Negation)
                    {
                        GroundedPredicate gp = (GroundedPredicate)gpEff.Negate();


                        foreach (Action actName in mapActToListForDelete[act.Name])
                        {
                            Action preAction = mapActionName[actName.Name];
                            foreach (GroundedPredicate preEff in preAction.Effects.GetAllPredicates())
                            {
                                if (!preEff.Negation)
                                {
                                    if (preEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                                    {
                                        if (!hash.Contains(preEff.Negate()))
                                        {
                                            eff.AddOperand(preEff.Negate());
                                            hash.Add(preEff.Negate());
                                        }
                                    }
                                }
                            }
                        }
                        break;

                    }
                }
                mapActionName[actionName].Effects = eff;
                mapActionName[actionName].LoadPrecondition();
            }
            return mapActionName;
        }
        Dictionary<Action, KeyValuePair<GroundedPredicate,List<Action>>> mapActionToActionList = null;
        Dictionary<GroundedPredicate, List<Action>> mapGpToAchivers = null;
        /* public List<Action> getAdvancedProjectionPublicAction2(int index, List<Predicate> newPredicates, State s)
         {
             mapGpToAchivers = new Dictionary<GroundedPredicate, List<Action>>();
             mapActionToActionList = new Dictionary<Action, KeyValuePair<GroundedPredicate, List<Action>>>();
             Dictionary<string, Action> mapActionName = new Dictionary<string, Action>();
             List<Action> allActions = new List<Action>();
             mapGpToArtificial = new Dictionary<GroundedPredicate, GroundedPredicate>();
             Dictionary<Action, GroundedPredicate> mapActionToArtificialEffect = new Dictionary<Action, GroundedPredicate>();


             ArtificialToPrivate = new Dictionary<GroundedPredicate, GroundedPredicate>();
             foreach (Action act in publicActions)
             {
                 Action newAction = new Action(act.Name);
                 newAction.Preconditions = act.Preconditions;
                 newAction.Effects = act.Effects;
                 newAction.LoadPrecondition();
                 mapActionName[act.Name] = newAction;

             }
             foreach (var actionName in mapActionName.Keys.ToList())
             {
                 bool flag = false;
                 Action act = mapActionName[actionName];
                 Program.sizeOfRegressionTree = 0;
                 List<Action> temporalActions = new List<Action>();
                 CompoundFormula pre = new CompoundFormula("and");
                 int globaDepth = 0;

                 GroundedPredicate newEffPredicate = null;
                 newEffPredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + index);
                 newPredicates.Add(newEffPredicate);
                 newPredicates.Add((GroundedPredicate)newEffPredicate.Negate());
                 CompoundFormula cf = new CompoundFormula("and");
                 cf.AddOperand(act.Effects);
                 cf.AddOperand(newEffPredicate);
                 act.Effects = cf;
                 act.LoadPrecondition();
                 mapActionToArtificialEffect.Add(act, newEffPredicate);
                 index++;
                 foreach (GroundedPredicate gpPre in act.Preconditions.GetAllPredicates())
                 {
                     if (gpPre.Name.Contains(Domain.ARTIFICIAL_PREDICATE) || PublicPredicates.Contains(gpPre))
                     {
                         pre.AddOperand(gpPre);
                     }
                     else
                     {
                         if (!mapGpToAchivers.ContainsKey(gpPre))
                         {
                             int depth1;
                             int depth2;
                             int tmp = Program.sizeOfRegressionTree;
                             HashSet<Action> Achievers = Distributed_Landmarks_Detection.GetPublicActionsLandmarks2(gpPre, this, out depth1, true);
                             if (Achievers.Count == 0)
                             {
                                 mapGpToAchivers.Add(gpPre, new List<Action>());
                                 continue;
                             }
                             flag = true;
                             List<Action> lAction = Achievers.ToList();
                             mapActionToActionList.Add(act, new KeyValuePair<GroundedPredicate, List<Action>>(gpPre, lAction));
                             mapGpToAchivers.Add(gpPre, lAction);
                             continue;
                         }
                         else
                         {
                             if (mapGpToAchivers[gpPre].Count == 0)
                             {
                                 continue;
                             }
                             mapActionToActionList.Add(act, new KeyValuePair<GroundedPredicate, List<Action>>(gpPre, mapGpToAchivers[gpPre]));
                             flag = true;
                             continue;
                         }

                     }
                 }
                 continue;
                 if(!flag)
                     mapActionToActionList.Add(act, new KeyValuePair<GroundedPredicate, List<Action>>(null, null));

             }

             List<Action> newActionSet = new List<Action>();
             foreach (var item in mapActionToActionList)
             {
                 if (item.Key != null)
                 {
                     bool dell = false;

                     if (item.Key.HashEffects.Contains((GroundedPredicate)item.Value.Key.Negate()))
                     {
                         dell = true;
                     }
                     foreach (Action depAct in item.Value.Value)
                     {
                         Action newAct = new Action(item.Key.Name);
                         CompoundFormula newEff = new CompoundFormula("and");
                         newEff.AddOperand(item.Key.Effects);
                         CompoundFormula newPre = new CompoundFormula("and");
                         newPre.AddOperand(item.Key.Preconditions);
                         newPre.AddOperand(mapActionToArtificialEffect[depAct]);
                         if(dell)
                         {
                             newEff.AddOperand(mapActionToArtificialEffect[depAct].Negate());
                         }
                         newAct.Effects = newEff;
                         newAct.Preconditions = newPre;
                         newAct.LoadPrecondition();

                     }

                     Action newInitialAct = new Action(item.Key.Name);
                     CompoundFormula newInitialEff = new CompoundFormula("and");
                     newInitialEff.AddOperand(item.Key.Effects);
                     CompoundFormula newInitialPre = new CompoundFormula("and");
                     newInitialPre.AddOperand(item.Key.Preconditions);
                     GroundedPredicate newEffPredicate = null;
                     newEffPredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + index);
                     newPredicates.Add(newEffPredicate);
                     newPredicates.Add((GroundedPredicate)newEffPredicate.Negate());
                     index++;
                     mapGpToArtificial.Add
                     newInitialPre.AddOperand(mapActionToArtificialEffect[depAct]);
                     if (dell)
                     {
                         newInitialEff.AddOperand(mapActionToArtificialEffect[depAct].Negate());
                     }
                     newInitialAct.Effects = newInitialEff;
                     newAInitialct.Preconditions = newInitialPre;
                     newInitialAct.LoadPrecondition();

                 }
             }


             foreach (var actionName in mapActionName.Keys.ToList())
             {
                 Action act = mapActionName[actionName];
                 CompoundFormula eff = new CompoundFormula("and");
                 foreach (GroundedPredicate gpEff in act.Effects.GetAllPredicates())
                 {
                     if (PublicPredicates.Contains(gpEff) || gpEff.Name.Contains(Domain.ARTIFICIAL_PREDICATE))
                     {
                         eff.AddOperand(gpEff);
                     }
                     else
                     {
                         if (gpEff.Negation)
                         {
                             GroundedPredicate gp = (GroundedPredicate)gpEff.Negate();
                             if (mapGpToArtificial.ContainsKey(gp))
                             {

                                 eff.AddOperand(mapGpToArtificial[gp].Negate());

                             }
                         }
                     }
                 }
                 mapActionName[actionName].Effects = eff;
                 mapActionName[actionName].LoadPrecondition();
             }
             return mapActionName.Values.ToList();
         }*/
        public List<Landmark> GetPublicGoals()
        {
            List<Landmark> lGoal = new List<Landmark>();
            foreach (GroundedPredicate g in goal)
            {
                if (PublicPredicates.Contains(g))
                {
                    Landmark l = new Landmark("Goal", true);
                    l.AddPublicFact(g, "fact");
                    lGoal.Add(l);
                }
                else
                {
                    lGoal.AddRange(Distributed_Landmarks_Detection.GetPublicLandmarks(g, this));
                }
            }
            return lGoal;
        }

        public List<GroundedPredicate> GetPublicfactsGoals()
        { 
            return publicGoals;
        }
        public void CalPublicfactsGoals()
        {
            publicGoals = new List<GroundedPredicate>();
            privateGoals = new List<GroundedPredicate>();
            foreach (GroundedPredicate g in goal)
            {
                if (PublicPredicates.Contains(g))
                {

                    publicGoals.Add(g);
                }
                else
                {
                    privateGoals.Add(g);
                }

            }
            
        }
        public void UpdateAproximtState(State s, bool[] actionsVector)
        {



            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;

                int i = 0;
                foreach (Action act in privateActions)
                {
                    if (actionsVector[i] == false)
                    {
                        if (Contains(s, act.HashPrecondition))
                        {

                            actionsVector[i] = true;
                            if (act.Effects != null)
                            {
                                foreach (GroundedPredicate addProp in act.HashEffects)
                                {
                                    if (!s.Predicates.Contains(addProp))
                                    {

                                        s.AddPredicate(addProp);

                                        flag2 = true;
                                    }

                                }
                            }

                        }
                    }

                    i++;
                }



            }

        }
        public List<Action> GetPublicActions(List<Action> actions)
        {
            List<Action> relevantActions = new List<Action>();
            foreach (Action act in actions)
            {
                if (publicActions.Contains(act))
                {
                    relevantActions.Add(act);
                }
            }
            return relevantActions;
        }

        public List<GroundedPredicate> GetPublicFacts(List<GroundedPredicate> facts)
        {
            List<GroundedPredicate> relevantFacts = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in facts)
            {
                if (PublicPredicates.Contains(gp))
                {
                    relevantFacts.Add(gp);
                }
            }
            return relevantFacts;
        }
        public List<PrivacyPreservingLandmark> FirstIteration()
        {
            WhatICanGetWithMyPrivate();
            /*foreach (GroundedPredicate prop in startState.Predicates)
            {
                Landmark tempLandmark = new Landmark("fact");
                tempLandmark.AddFact(prop, "Start");
                bool flg = InserLandmark(tempLandmark, null, null);
            }*/
            discoverdLandmark = new List<Landmark>();
            List<PrivacyPreservingLandmark> PrivacyPreservingLandmarks = new List<PrivacyPreservingLandmark>();
            foreach (GroundedPredicate g in goal)
            {
                PrivacyPreservingLandmark ppLandmark = new PrivacyPreservingLandmark();
                ppLandmark.isGoal = true;
                if (PublicPredicates.Contains(g))
                {
                    Landmark landmark = new Landmark("fact", true);
                    landmark.AddFact(g, "Goal");
                    landmark.worth = 2;
                    bool flg = InserLandmark("Public", landmark, null, null);

                    ppLandmark.AddPublicLandmark(landmark);
                    publicLandmarks.Add(landmark);
                    if (!flg)
                    {
                        ppLandmark.toDevelop = false;
                    }



                }
                else
                {
                    Landmark landmark = new Landmark("fact", true);
                    landmark.AddFact(g, "Goal");
                    landmark.worth = 2;
                    bool flg = InserLandmark("Private", landmark, null, null);


                    ppLandmark.AddPrivateLandmark(landmark, name);
                    publicLandmarks.Add(landmark);
                    if (!flg)
                    {
                        ppLandmark.toDevelop = false;
                    }

                }
                PrivacyPreservingLandmarks.Add(ppLandmark);

            }
            return PrivacyPreservingLandmarks;
        }

        public void Reset()
        {

            exploreLandmarks = null;
            //isMyLandmarks = false;
        }

        public void SetLandmarkToExplorer(PrivacyPreservingLandmark ppLandmark)
        {

            exploreLandmarks = ppLandmark.GetAgentLandmark(name);



        }
        public void SetLandmarkToExplorer(Landmark ppLandmark)
        {

            exploreLandmarks = ppLandmark;


        }
        
        public KeyValuePair<Landmark, string> ChooseLocalLandmarkToExplorer()
        {
            if (localPrivateLandmarks.Count > 0)
            {
                exploreLandmarks = localPrivateLandmarks.Dequeue();
                isMyLandmarks = true;
                return new KeyValuePair<Landmark, string>(null, "Private");
            }

            return new KeyValuePair<Landmark, string>(null, null); ;
        }

        public HashSet<GroundedPredicate> Detection()
        {
            // Landmark l = ppLandmarks.GetMyLandmark(name);


            //  bool otherAgentLandmarks=false;
            //  if (exploreLandmarks == null)
            // {
            //      exploreLandmarks = l;
            // otherAgentLandmarks=true;
            //   }

            temporalActionsCanGet = new List<Action>();
            temporalActionsNontGet = new HashSet<Action>();
            iCanGet = new HashSet<GroundedPredicate>();

            foreach (Action act in m_actions)
            {

                bool flag = true;
                if (exploreLandmarks != null)
                {
                    foreach (KeyValuePair<GroundedPredicate, string> prop in exploreLandmarks.facts)
                    {
                        if (act.Effects != null)
                        {
                            if (act.HashEffects.Contains(prop.Key))
                            {
                                temporalActionsCanGet.Add(act);
                                flag = false;
                                break;
                            }
                        }

                    }
                }
                if (flag)
                {
                    temporalActionsNontGet.Add(act);
                }
            }

            // if(otherAgentLandmarks && l!=null && temporalActionsCanGet.Count > 0)
            // {
            //      otherAgentLandmarks = InserLandmark(l, null, null);

            //  }

            foreach (GroundedPredicate prop in startState.Predicates)
            {

                iCanGet.Add(prop);
            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp))
                                {

                                    iCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);

                }

            }
            publiciCanGet = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    publiciCanGet.Add(gp);
                }
            }
            return publiciCanGet;

        }
        public HashSet<GroundedPredicate> DetectionFrom(int index)
        {
            //StateInfo oldState = hashOfStates.ElementAt(index).Key;
            StateInfo oldState = mapToState[index]; 
            // Landmark l = ppLandmarks.GetMyLandmark(name);


            //  bool otherAgentLandmarks=false;
            //  if (exploreLandmarks == null)
            // {
            //      exploreLandmarks = l;
            // otherAgentLandmarks=true;
            //   }

            temporalActionsCanGet = new List<Action>();
            temporalActionsNontGet = new HashSet<Action>();
            iCanGet = new HashSet<GroundedPredicate>();

            foreach (Action act in m_actions)
            {

                bool flag = true;
                if (exploreLandmarks != null)
                {
                    foreach (KeyValuePair<GroundedPredicate, string> prop in exploreLandmarks.facts)
                    {
                        if (act.Effects != null)
                        {
                            if (act.HashEffects.Contains(prop.Key))
                            {
                                temporalActionsCanGet.Add(act);
                                flag = false;
                                break;
                            }
                        }

                    }
                }
                if (flag)
                {
                    temporalActionsNontGet.Add(act);
                }
            }

            // if(otherAgentLandmarks && l!=null && temporalActionsCanGet.Count > 0)
            // {
            //      otherAgentLandmarks = InserLandmark(l, null, null);

            //  }

            foreach (GroundedPredicate prop in oldState.state.Predicates)
            {

                iCanGet.Add(prop);
            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp))
                                {

                                    iCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);

                }

            }
            publiciCanGet = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    publiciCanGet.Add(gp);
                }
            }
            return publiciCanGet;

        }
        public HashSet<GroundedPredicate> InitHspGraph(int index)
        {
            relaxtionPlan=new List<Action>();
            PreferablesActions = new Dictionary<GroundedPredicate, Action>();
            //StateInfo oldState = hashOfStates.ElementAt(index).Key;
            StateInfo oldState = mapToState[index]; 
            // Landmark l = ppLandmarks.GetMyLandmark(name);


            //  bool otherAgentLandmarks=false;
            //  if (exploreLandmarks == null)
            // {
            //      exploreLandmarks = l;
            // otherAgentLandmarks=true;
            //   }

            hspGraph = new Dictionary<GroundedPredicate, int>();
            iCanGet = new HashSet<GroundedPredicate>();
            temporalActionsNontGet = new HashSet<Action>(m_actions);
            HashSet<GroundedPredicate> addList = null;
            foreach (GroundedPredicate prop in oldState.state.Predicates)
            {

                iCanGet.Add(prop);
                hspGraph.Add(prop, 0);
                PreferablesActions.Add(prop, null);
            }
            bool flag2 = true;
            level = 1;
          //  while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();
                addList = new HashSet<GroundedPredicate>();
                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp) & !addList.Contains(addProp))
                                {
                                    addList.Add(addProp);
                                    PreferablesActions.Add(addProp, act);
                                    //iCanGet.Add(addProp);
                                    flag2 = true;
                                }

                            }
                        }

                    }


                }
                foreach (GroundedPredicate addP in addList)
                {
                    hspGraph.Add(addP, level);
                    
                    iCanGet.Add(addP);
                }
                
                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);
                }

            }
            publiciCanGet = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    publiciCanGet.Add(gp);
                }
            }
            return publiciCanGet;

        }
        public bool[] PotentialToAchieve()
        {
            bool[] ans = new bool[publicLandmarks.Count];
            int index = 0;
            foreach (Landmark l in publicLandmarks)
            {
                foreach (GroundedPredicate gp in l.facts.Keys)
                {
                    if (iCanGet.Contains(gp))
                    {
                        ans[index] = true;
                    }


                }
                index++;
            }
            return ans;
        }
        public int[] PotentialGoalToAchieve()
        {
            int[] goalCost = new int[allGoals.Count];
            int index = 0;
            foreach (GroundedPredicate gp in allGoals)
            {

                if (hspGraph.ContainsKey(gp))
                {
                    goalCost[index]=hspGraph[gp];
                }
                else
                {
                    goalCost[index] = -1;
                }
                index++;
            }
            return goalCost;
        }
        public bool[] PotentialToAchieve(List<Landmark>goals)
        {
            bool[] ans = new bool[goals.Count];
            int index = 0;
            foreach (Landmark l in goals)
            {
                foreach (GroundedPredicate gp in l.facts.Keys)
                {
                    if (iCanGet.Contains(gp))
                    {
                        ans[index] = true;
                    }


                }
                index++;
            }
            return ans;
        }
        public HashSet<GroundedPredicate> DetectionLocal(Landmark l, Landmark publicLandmark)
        {
            bool otherAgentLandmarks = false;
            if (exploreLandmarks == null)
            {
                exploreLandmarks = l;
                otherAgentLandmarks = true;
            }
            temporalActionsCanGet = new List<Action>();
            temporalActionsNontGet = new HashSet<Action>();
            iCanGet = new HashSet<GroundedPredicate>();

            foreach (Action act in m_actions)
            {

                bool flag = true;
                if (exploreLandmarks != null)
                {
                    foreach (KeyValuePair<GroundedPredicate, string> prop in exploreLandmarks.facts)
                    {
                        if (act.Effects != null)
                        {
                            if (act.HashEffects.Contains(prop.Key))
                            {
                                temporalActionsCanGet.Add(act);
                                flag = false;
                                break;
                            }
                        }

                    }
                }
                if (flag)
                {
                    foreach (KeyValuePair<GroundedPredicate, string> prop in publicLandmark.facts)
                    {
                        if (act.Effects != null)
                        {
                            if (act.HashEffects.Contains(prop.Key))
                            {
                                temporalActionsCanGet.Add(act);
                                flag = false;
                                break;
                            }
                        }

                    }

                }
                if (flag)
                {
                    temporalActionsNontGet.Add(act);
                }
            }

            if (otherAgentLandmarks && l != null && temporalActionsCanGet.Count > 0)
            {
                otherAgentLandmarks = InserLandmark(l, null, null);

            }

            foreach (GroundedPredicate prop in startState.Predicates)
            {

                iCanGet.Add(prop);
            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp))
                                {

                                    iCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);

                }

            }
            publiciCanGet = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    publiciCanGet.Add(gp);
                }
            }
            return publiciCanGet;

        }
        public HashSet<GroundedPredicate> DetectionGlobal()
        {
            // Landmark l = ppLandmarks.GetMyLandmark(name);


            //  bool otherAgentLandmarks=false;
            //  if (exploreLandmarks == null)
            // {
            //      exploreLandmarks = l;
            // otherAgentLandmarks=true;
            //   }

            temporalActionsCanGet = new List<Action>();
            temporalActionsNontGet = new HashSet<Action>();
            iCanGet = new HashSet<GroundedPredicate>();

            foreach (Action act in m_actions)
            {

                bool flag = true;
                if (exploreLandmarks != null)
                {
                    foreach (KeyValuePair<GroundedPredicate, string> prop in exploreLandmarks.facts)
                    {
                        if (act.Effects != null)
                        {
                            if (act.HashEffects.Contains(prop.Key))
                            {
                                temporalActionsCanGet.Add(act);
                                //flag = false;
                                break;
                            }
                        }

                    }
                }
                if (flag)
                {
                    temporalActionsNontGet.Add(act);
                }
            }

            // if(otherAgentLandmarks && l!=null && temporalActionsCanGet.Count > 0)
            // {
            //      otherAgentLandmarks = InserLandmark(l, null, null);

            //  }

            foreach (GroundedPredicate prop in startState.Predicates)
            {

                iCanGet.Add(prop);
            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp))
                                {

                                    iCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);

                }

            }
            publiciCanGet = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    publiciCanGet.Add(gp);
                }
            }
            return publiciCanGet;

        }
        public void UpDateWhatICanGet(Landmark l2)
        {
            temporalActionsNontGet = new HashSet<Action>();
            bool flag;
            foreach (Action act in m_actions)
            {
                flag = false;
                foreach (GroundedPredicate gp in l2.facts.Keys)
                {
                    if (act.HashEffects.Contains(gp.Negate()))
                    {
                        flag = true;
                        break;
                    }
                }
                if (!flag)
                {
                    temporalActionsNontGet.Add(act);
                }
            }
        }
        public KeyValuePair<bool, HashSet<GroundedPredicate>> UpdateHspGraph(HashSet<GroundedPredicate> OtherCanGet, int level,out bool isLocalGoal)
        {
           
            foreach (GroundedPredicate gp in OtherCanGet)
            {
                if (!iCanGet.Contains(gp))
                {
                    iCanGet.Add(gp);
                }
            }

       
            HashSet<GroundedPredicate> addList = new HashSet<GroundedPredicate>();
            bool flag2 = true;
            
            //while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp) && !addList.Contains(addProp))
                                {
                                    addList.Add(addProp);
                                   // iCanGet.Add(addProp);
                                    PreferablesActions.Add(addProp, act);
                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (GroundedPredicate addP in addList)
                {
                    hspGraph.Add(addP, level);
                    iCanGet.Add(addP);
                }
              
                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);
                }
                

            }
            HashSet<GroundedPredicate> addingPublicPredicate = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    if (!publiciCanGet.Contains(gp))
                    {
                        publiciCanGet.Add(gp);
                        if (!OtherCanGet.Contains(gp))
                        {
                            addingPublicPredicate.Add(gp);
                        }
                    }
                }
            }
           
            isLocalGoal = true;
            foreach (GroundedPredicate gp in goal)
            {
                if (!iCanGet.Contains(gp))
                {
                    isLocalGoal = false;
                    break;
                }
            }
            return new KeyValuePair<bool,HashSet<GroundedPredicate>>(flag2,addingPublicPredicate);

        }
        public void InitRelaxtionPlan()
        {
            relaxGoals = new List<GroundedPredicate>(privateGoals);
            //AllLocalGoals = new HashSet<GroundedPredicate>(goal);
            
            AchievedFacts = new HashSet<GroundedPredicate>();
        }
        public List<GroundedPredicate> UpDateRelaxtionPlan(HashSet<GroundedPredicate> publicGoals,out string flag)
        {
            List<GroundedPredicate> newPublicGoals = new List<GroundedPredicate>();
            try
            {
                HashSet<GroundedPredicate> tmpLayerGoals = new HashSet<GroundedPredicate>();
                for (int i = 0; i < relaxGoals.Count; i++)
                {
                    GroundedPredicate gp = relaxGoals.ElementAt(i);
                    if (AchievedFacts.Contains(gp))
                    {
                        //relaxGoals.RemoveAt(i);
                        //i--;
                        continue;
                    }
                    if (PreferablesActions.ContainsKey(gp))
                    {
                        // relaxGoals.RemoveAt(i);
                        // i--;
                        Action act = PreferablesActions[gp];
                        if (act != null)
                        {
                            relaxtionPlan.Add(act);
                            AchievedFacts.Add(gp);
                            /*foreach (GroundedPredicate eff in act.HashEffects)
                            {
                                AchievedFacts.Add(eff);
                            }*/
                            foreach (GroundedPredicate pre in act.HashPrecondition)
                            {
                                if (!AchievedFacts.Contains(pre))
                                {
                                    tmpLayerGoals.Add(pre);
                                }
                            }
                        }

                    }
                    else
                    {
                        flag = "fail";
                        return null;
                    }

                }
                for (int i = 0; i < publicGoals.Count; i++)
                {
                    GroundedPredicate gp = publicGoals.ElementAt(i);
                    if (AchievedFacts.Contains(gp))
                    {
                        publicGoals.Remove(gp);
                        i--;
                        continue;
                    }
                    if (PreferablesActions.ContainsKey(gp))
                    {
                        publicGoals.Remove(gp);
                        i--;
                        Action act = PreferablesActions[gp];
                        AchievedFacts.Add(gp);
                        if (act != null)
                        {
                            relaxtionPlan.Add(act);
                            
                            /* foreach (GroundedPredicate eff in act.HashEffects)
                             {
                                 AchievedFacts.Add(eff);
                             }*/
                            foreach (GroundedPredicate pre in act.HashPrecondition)
                            {
                                if (!AchievedFacts.Contains(pre))
                                {
                                    tmpLayerGoals.Add(pre);
                                }
                            }
                        }

                    }
                }
                if (tmpLayerGoals.Count > 0)
                    flag = "continue";
                else
                    flag = "finsh";
                
                for (int i = 0; i < tmpLayerGoals.Count; i++)
                {
                    GroundedPredicate gp = tmpLayerGoals.ElementAt(i);
                    
                    if (PublicPredicates.Contains(gp))
                    {
                        tmpLayerGoals.Remove(gp);
                        i--;
                        newPublicGoals.Add(gp);
                    }
                }
                relaxGoals = tmpLayerGoals.ToList();
            }
            catch (Exception ex)
            {
                flag = "dd";
                return null;
            }
            return newPublicGoals;
        }
        public bool[] SatisfactiedLandmarksOnRelaxPlan(bool[] satVector)
        {
            HashSet<GroundedPredicate> relaxEff = new HashSet<GroundedPredicate>();
            foreach (Action act in relaxtionPlan)
            {
                foreach (GroundedPredicate eff in act.HashEffects)
                    relaxEff.Add(eff);
            }
            bool[] ansVector = new bool[satVector.Length];
            for (int i = 0; i < satVector.Length; i++)
            {
                if (satVector[i] == false)
                {

                    foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                    {
                        if (relaxEff.Contains(fact))
                        {
                            ansVector[i] = true;
                            break;
                        }
                    }

                }
                else
                {
                    ansVector[i] = true;
                }
            }
            return ansVector;
        }
        public int GetRelaxPlanSize()
        {
            return relaxtionPlan.Count;
        }
        public void GetPublicPreRelax(int index,HashSet<GroundedPredicate> pubFact)
        {
            StateInfo oldState = mapToState[index];
            AllLocalGoals = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in goal)
            {
                if (!oldState.state.Contains(gp))
                {
                    AllLocalGoals.Add(gp);
                    if (PublicPredicates.Contains(gp))
                        pubFact.Add(gp);
                }
            }
            foreach (Action act in relaxtionPlan)
            {
                foreach (GroundedPredicate gp in act.HashPrecondition)
                {
                    if (!oldState.state.Contains(gp))
                    {
                        AllLocalGoals.Add(gp);
                        if (PublicPredicates.Contains(gp))
                            pubFact.Add(gp);
                    }
                }
            }
            
        }
        public HashSet<string> ComputePreferActions(HashSet<GroundedPredicate> pubFact)
        {
            HashSet<string> PreferdActions=new HashSet<string>();
            foreach (GroundedPredicate gp in pubFact)
            {
                AllLocalGoals.Add(gp);
            }

            foreach (Action act in publicActions)
            {
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (AllLocalGoals.Contains(gp))
                        PreferdActions.Add(act.Name);
                }
            }
            return PreferdActions;
        }
        public HashSet<GroundedPredicate> WhatYoCanGet(HashSet<GroundedPredicate> OtherCanGet)
        {
            foreach (GroundedPredicate gp in OtherCanGet)
            {
                if (!iCanGet.Contains(gp))
                {
                    iCanGet.Add(gp);
                }

            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();

                foreach (Action act in temporalActionsNontGet)
                {
                    if (Contains(iCanGet, act.HashPrecondition))
                    {
                        tempActionList.Add(act);

                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!iCanGet.Contains(addProp))
                                {

                                    iCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }

                foreach (Action action in tempActionList)
                {
                    temporalActionsNontGet.Remove(action);

                }

            }
            HashSet<GroundedPredicate> addingPublicPredicate = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in iCanGet)
            {
                if (PublicPredicates.Contains(gp))
                {
                    if (!publiciCanGet.Contains(gp))
                    {
                        publiciCanGet.Add(gp);
                        if (!OtherCanGet.Contains(gp))
                        {
                            addingPublicPredicate.Add(gp);
                        }
                    }
                }
            }
            return addingPublicPredicate;

        }
        public List<Action> CanGet()
        {

            if (exploreLandmarks == null)
                return null;
            PossibleBefore = new List<Action>();
            foreach (Action act in temporalActionsCanGet)
            {

                if (Contains(iCanGet, act.HashPrecondition))
                {
                    PossibleBefore.Add(act);
                }
            }
            if (PossibleBefore.Count == 0)
                return null;
            return PossibleBefore;


        }


        public List<PrivacyPreservingLandmark> DetectNewLandmarks()
        {
            int indexProp = 1;
            Dictionary<string,int> map = new Dictionary<string,int>();
            if (temporalActionsCanGet.Count == 0)
                return null;
            List<PrivacyPreservingLandmark> newsPPLandmarks = new List<PrivacyPreservingLandmark>();
            bool b = isMyLandmarks;
            bool flag2 = false;
            if (PossibleBefore.Count > 0)
            {
                HashSet<GroundedPredicate> oldFacts = new HashSet<GroundedPredicate>();
                Action firstAction = PossibleBefore[0];
                foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                {
                    bool flag = true;
                    foreach (Action act in PossibleBefore)
                    {
                        if (!act.HashPrecondition.Contains(prop))
                        {
                            flag = false;
                            break;
                        }
                    }
                    if (flag)
                    {
                        string type = "Private";
                        if (PublicPredicates.Contains(prop))
                            type = "Public";
                        Landmark newLandmark = new Landmark("fact", false);
                        newLandmark.AddFact(prop, "first_round");
                        bool flg = InserLandmark(type, newLandmark, exploreLandmarks, "greedy-necessary");
                        oldFacts.Add(prop);
                        if (flg)
                        {
                            PrivacyPreservingLandmark ppLandmark = new PrivacyPreservingLandmark();
                            if (type.Equals("Private"))
                            {

                                ppLandmark.AddPrivateLandmark(newLandmark, name);

                            }

                            if (type.Equals("Public"))
                            {

                                ppLandmark.AddPublicLandmark(newLandmark);

                            }
                            if (!map.ContainsKey(prop.Name))
                            {
                                indexProp = 1;
                                map.Add(prop.Name, 2);
                            }
                            else
                            {
                                indexProp = map[prop.Name];
                                map[prop.Name]++;
                            }

                            ppLandmark.type = prop.Name + indexProp.ToString();
                            indexProp++;
                            newsPPLandmarks.Add(ppLandmark);
                        }

                    }
                }
                if (!flag2 && PossibleBefore.Count > 1) //&& landmark.facts.Count < 2)
                {
                    flag2 = true;
                    firstAction = PossibleBefore[0];
                    PossibleBefore.RemoveAt(0);

                    foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                    {
                        string type = prop.Name;
                        if (!startState.Contains(prop) && !oldFacts.Contains(prop))
                        {
                            int counter = 0; ;
                            Landmark newLandmark = new Landmark("Disjunctive", false);
                            //newLandmark.worth = exploreLandmarks.worth - 10;
                            newLandmark.AddFact(prop, "first_round");

                            foreach (Action act in PossibleBefore)
                            {
                                bool f = false;
                                foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                {
                                    if (prop2.Name == prop.Name && !startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                    {

                                        if (!newLandmark.facts.ContainsKey(prop2))
                                        {
                                            newLandmark.AddFact(prop2, "first_round");
                                        }
                                        counter++;
                                        f = true;
                                        break;
                                    }
                                }
                                /* if (!f)
                                 {
                                     foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                     {
                                         if (!startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                         {

                                             if (!newLandmark.facts.ContainsKey(prop2))
                                             {

                                                 newLandmark.AddFact(prop2, "first_round");
                                             }
                                             counter++;
                                             f = true;
                                             break;
                                         }
                                     }
                                 }*/

                            }
                            if (counter == PossibleBefore.Count && newLandmark.facts.Count > 1)
                            {
                                PrivacyPreservingLandmark ppLandmark = new PrivacyPreservingLandmark();
                                string pub = "Public";
                                foreach (GroundedPredicate fact in newLandmark.facts.Keys)
                                {

                                    if (PublicPredicates.Contains(fact))
                                    {
                                        ppLandmark.AddPublicPredicate(fact);
                                    }
                                    else
                                    {
                                        ppLandmark.AddPrivatePredicate(fact, name);
                                        pub = "Private";
                                    }
                                }
                                bool flg = InserLandmark(pub, newLandmark, exploreLandmarks, "greedy-necessary");
                                if (flg)
                                {
                                    if (!map.ContainsKey(prop.Name))
                                    {
                                        indexProp = 1;
                                        map.Add(prop.Name, 2);
                                    }
                                    else
                                    {
                                        indexProp = map[prop.Name];
                                        map[prop.Name]++;
                                    }
                                    ppLandmark.type = type + indexProp.ToString();
                                    indexProp++;
                                    newsPPLandmarks.Add(ppLandmark);
                                }
                            }
                        }
                    }
                }
            }
            return newsPPLandmarks;
        }
        public void DetectNewLocalLandmarks2(bool toDevelop)
        {
            if (temporalActionsCanGet.Count == 0) return;


            bool flag2 = false;
            if (PossibleBefore.Count > 0)
            {
                if (toDevelop)
                {
                    HashSet<GroundedPredicate> oldFacts = new HashSet<GroundedPredicate>();
                    Action firstAction = PossibleBefore[0];
                    foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                    {
                        bool flag = true;
                        foreach (Action act in PossibleBefore)
                        {
                            if (!act.HashPrecondition.Contains(prop))
                            {
                                flag = false;
                                break;
                            }
                        }
                        if (flag)
                        {


                            //if (!problam.StartState.Contains(prop))
                            // {
                            string type = "Private";
                            if (PublicPredicates.Contains(prop))
                                type = "Public";
                            Landmark newLandmark = new Landmark("fact", false);
                            newLandmark.AddFact(prop, "first_round");
                            //newLandmark.worth = exploreLandmarks.worth - 10;
                            oldFacts.Add(prop);
                            bool flg = InserLocalLandmark(newLandmark, exploreLandmarks, "greedy-necessary");
                            if (flg)
                            {
                                if (type == "Private")
                                {
                                    localPrivateLandmarks.Enqueue(newLandmark);
                                }

                                if (type == "Public")
                                {
                                    localPublicLandmarks.Enqueue(newLandmark);
                                }
                            }
                            // }
                        }
                    }
                    if (!flag2 && PossibleBefore.Count > 1) //&& landmark.facts.Count < 2)
                    {
                        flag2 = true;
                        firstAction = PossibleBefore[0];
                        PossibleBefore.RemoveAt(0);
                        foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                        {
                            if (!startState.Contains(prop) && !oldFacts.Contains(prop))
                            {
                                int counter = 0; ;
                                Landmark newLandmark = new Landmark("Disjunctive", false);
                                //newLandmark.worth = exploreLandmarks.worth - 10;
                                newLandmark.AddFact(prop, "first_round");
                                foreach (Action act in PossibleBefore)
                                {
                                    bool f = false;
                                    foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                    {
                                        if (prop2.Name == prop.Name && !startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                        {

                                            if (!newLandmark.facts.ContainsKey(prop2))
                                            {
                                                newLandmark.AddFact(prop2, "first_round");
                                            }
                                            counter++;
                                            f = true;
                                            break;
                                        }
                                    }
                                    if (!f)
                                    {
                                        foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                        {
                                            if (!startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                            {

                                                if (!newLandmark.facts.ContainsKey(prop2))
                                                {

                                                    newLandmark.AddFact(prop2, "first_round");
                                                }
                                                counter++;
                                                f = true;
                                                break;
                                            }
                                        }
                                    }

                                }
                                if (counter == PossibleBefore.Count && newLandmark.facts.Count > 1)
                                {
                                    bool flg = InserLocalLandmark(newLandmark, exploreLandmarks, "greedy-necessary");
                                    if (flg)
                                    {
                                        PrivacyPreservingLandmark ppLandmark = new PrivacyPreservingLandmark();

                                        foreach (GroundedPredicate fact in newLandmark.facts.Keys)
                                        {

                                            if (PublicPredicates.Contains(fact))
                                            {
                                                ppLandmark.AddPublicPredicate(fact);
                                            }
                                            else
                                            {
                                                ppLandmark.AddPrivatePredicate(fact, name);
                                            }
                                        }

                                    }

                                }
                            }
                        }
                    }
                }
            }
        }

        public List<Landmark> GetLastsPublicLandmarks()
        {
            var ans = localPublicLandmarks.ToList();
            localPublicLandmarks = new Queue<Landmark>();
            return ans;
        }

        public bool AddPublicLandmarks(Landmark l)
        {
            bool flag = InserLandmark(l, null, null);
            if (flag)
                standByPublicLandmarks.Enqueue(l);
            return flag;
        }

        public int GetNumberOfRestLandmarks()
        {
            int money = 0;
            foreach (Landmark l in publicRelevantLandmark)
                money += l.worth;
            return money;
        }

        private bool InserLandmark(string type, Landmark land, Landmark land2, string orderType)
        {

            if (type.Equals("Public"))
            {

                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {                   
                    if (allPrivateLandmarks)
                    {
                        if (startState.m_lPredicates.Contains(fact.Key))
                            return false;
                    }
                    else
                    {
                        if (privateCanGet.Contains(fact.Key))
                            return false;
                    }
                }
                return true;
            }
            else
            {
                return InserPrivateLandmark(land, land2, orderType);
            }
        }
        private bool InserLandmark(Landmark land, Landmark land2, string orderType)
        {
            throw new NotImplementedException();
            return false;

        }
        private bool InserPrivateLandmark(Landmark land, Landmark land2, string orderType)
        {




            if (land.type == "fact")
            {
                Landmark delLandmark = null;
                bool flag = true;
                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {
                    if (allPrivateLandmarks)
                    {
                        if (startState.m_lPredicates.Contains(fact.Key))
                            return false;
                    }
                    else
                    {
                        if (privateCanGet.Contains(fact.Key))
                            return false;
                    }
                    foreach (Landmark tmp in discoverdLandmark)
                    {
                        if (tmp.facts.ContainsKey(fact.Key))
                        {
                            if (tmp.type == "fact")
                            {

                                if (orderType != null)
                                {
                                    Order order = new Order(orderType, tmp, land2);
                                    orderList.Add(order);
                                }

                                return false;
                            }
                            delLandmark = tmp;
                            flag = false;
                            break;

                        }

                    }

                }
                if (!flag)
                {
                    discoverdLandmark.Remove(delLandmark);
                    List<Order> temList = new List<Order>();
                    foreach (Order order in orderList)
                    {
                        if (System.Object.ReferenceEquals(order.lendmark1, delLandmark) || System.Object.ReferenceEquals(order.lendmark2, delLandmark)) ;
                        {
                            temList.Add(order);
                        }
                    }

                    foreach (Order delOrder in temList)
                    {
                        orderList.Remove(delOrder);
                    }



                }

                discoverdLandmark.Add(land);
                if (orderType != null)
                {
                    Order order = new Order(orderType, land, land2);
                    orderList.Add(order);
                }
                return true;





            }

            if (land.type == "Disjunctive")
            {
                Landmark delLandmark = null;
                bool flag = true;
                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {
                    if (allPrivateLandmarks)
                    {
                        if (startState.m_lPredicates.Contains(fact.Key))
                            return false;
                    }
                    else
                    {
                        if (privateCanGet.Contains(fact.Key))
                            return false;
                    }
                    if (!flag) break;
                    foreach (Landmark tmp in discoverdLandmark)
                    {
                        if (tmp.facts.ContainsKey(fact.Key))
                        {

                            delLandmark = tmp;
                            flag = false;
                            break;

                        }

                    }

                }

                if (flag)
                {
                    discoverdLandmark.Add(land);
                    if (orderType != null)
                    {
                        Order order = new Order(orderType, land, land2);
                        orderList.Add(order);
                    }
                    return true;
                }
                else
                {
                    if (delLandmark.facts.Count > land.facts.Count)
                    {
                        discoverdLandmark.Remove(delLandmark);
                        List<Order> temList = new List<Order>();
                        foreach (Order order in orderList)
                        {
                            if (System.Object.ReferenceEquals(order.lendmark1, delLandmark) || System.Object.ReferenceEquals(order.lendmark2, delLandmark))
                            {
                                temList.Add(order);
                            }


                        }

                        foreach (Order delOrder in temList)
                        {
                            orderList.Remove(delOrder);
                        }

                        discoverdLandmark.Add(land);
                        if (orderType != null)
                        {
                            Order order = new Order(orderType, land, land2);
                            orderList.Add(order);
                        }
                        return true;
                    }
                    else
                        return false;
                }
            }
            return false;
        }
        public List<Landmark> DetectNewLocalLandmarks(bool skipPublic)
        {
            int indexProp = 1;
            if (temporalActionsCanGet.Count == 0)
                return null;
            List<Landmark> newsPPLandmarks = new List<Landmark>();
            bool b = isMyLandmarks;
            bool flag2 = false;
            if (PossibleBefore.Count > 0)
            {
                HashSet<GroundedPredicate> oldFacts = new HashSet<GroundedPredicate>();
                Action firstAction = PossibleBefore[0];
                foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                {
                    bool flag = true;
                    foreach (Action act in PossibleBefore)
                    {
                        if (!act.HashPrecondition.Contains(prop))
                        {
                            flag = false;
                            break;
                        }
                    }
                    if (flag)
                    {
                        string type = "Private";
                        if (PublicPredicates.Contains(prop))
                            type = "Public";
                        Landmark newLandmark = new Landmark("fact", false);
                        newLandmark.AddFact(prop, "first_round");
                        bool flg = InserLocalLandmark(newLandmark, exploreLandmarks, "greedy-necessary");
                        oldFacts.Add(prop);
                        if (flg)
                        {
                            //localDiscoverdLandmark.Add(newLandmark);
                            if (type.Equals("Private"))
                            {

                                newLandmark.isPublic = false;

                            }

                            if (type.Equals("Public"))
                            {

                                newLandmark.isPublic = true;
                                if (skipPublic)
                                {
                                    continue;
                                }
                            }

                            indexProp++;
                            newLandmark.depth = exploreLandmarks.depth + 1;
                           /* if (Program.maxDepthOfRegressionTree < newLandmark.depth)
                            {
                                Program.maxDepthOfRegressionTree = newLandmark.depth;
                            }*/
                            newsPPLandmarks.Add(newLandmark);
                        }

                    }
                }
                if (!flag2 && PossibleBefore.Count > 1) //&& landmark.facts.Count < 2)
                {
                    flag2 = true;
                    firstAction = PossibleBefore[0];
                    PossibleBefore.RemoveAt(0);

                    foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                    {
                        string type = prop.Name;
                        if (!startState.Contains(prop) && !oldFacts.Contains(prop))
                        {
                            int counter = 0; ;
                            Landmark newLandmark = new Landmark("Disjunctive", false);
                            //newLandmark.worth = exploreLandmarks.worth - 10;
                            newLandmark.AddFact(prop, "first_round");

                            foreach (Action act in PossibleBefore)
                            {
                                bool f = false;
                                foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                {
                                    if (prop2.Name == prop.Name && !startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                    {

                                        if (!newLandmark.facts.ContainsKey(prop2))
                                        {
                                            newLandmark.AddFact(prop2, "first_round");
                                        }
                                        counter++;
                                        f = true;
                                        break;
                                    }
                                }
                                /* if (!f)
                                 {
                                     foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                     {
                                         if (!startState.Contains(prop2) && !oldFacts.Contains(prop2))
                                         {

                                             if (!newLandmark.facts.ContainsKey(prop2))
                                             {

                                                 newLandmark.AddFact(prop2, "first_round");
                                             }
                                             counter++;
                                             f = true;
                                             break;
                                         }
                                     }
                                 }*/

                            }
                            if (counter == PossibleBefore.Count && newLandmark.facts.Count > 1)
                            {

                                bool isPublic = true;
                                bool isPrivate = true;

                                foreach (GroundedPredicate fact in newLandmark.facts.Keys)
                                {

                                    if (!PublicPredicates.Contains(fact))
                                    {
                                        isPublic = false;
                                    }
                                    else
                                    {
                                        isPrivate = false;
                                    }


                                }
                                if (skipPublic)
                                {
                                    if (!isPrivate)
                                        continue;
                                }
                                newLandmark.isPublic = isPublic;

                                bool flg = InserLocalLandmark(newLandmark, exploreLandmarks, "greedy-necessary");
                                if (flg)
                                {
                                    //localDiscoverdLandmark.Add(newLandmark);
                                    newLandmark.depth = exploreLandmarks.depth + 1;
                                    /*if (Program.maxDepthOfRegressionTree < newLandmark.depth)
                                    {
                                        Program.maxDepthOfRegressionTree = newLandmark.depth;
                                    }*/
                                    newsPPLandmarks.Add(newLandmark);
                                }
                            }
                        }
                    }
                }
            }
            return newsPPLandmarks;
        }

        private bool InserLocalLandmark(Landmark land, Landmark land2, string orderType)
        {
            if (localDiscoverdLandmark == null)
            {
                throw new NotImplementedException();
                return false;
            }

            if (land.type == "fact")
            {
                Landmark delLandmark = null;
                bool flag = true;
                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {
                    if (allPrivateLandmarks)
                    {
                        if (startState.m_lPredicates.Contains(fact.Key))
                            return false;
                    }
                    else
                    {
                        if (privateCanGet.Contains(fact.Key))
                            return false;
                    }
                    foreach (Landmark tmp in localDiscoverdLandmark)
                    {
                        if (tmp.facts.ContainsKey(fact.Key))
                        {
                            if (tmp.facts.Count == 1)
                            {

                                /*if (orderType != null)
                                {
                                    Order order = new Order(orderType, tmp, land2);
                                    orderList.Add(order);
                                }*/

                                return false;
                            }
                            delLandmark = tmp;
                            flag = false;
                            break;

                        }

                    }

                }
                if (!flag)
                {
                    localDiscoverdLandmark.Remove(delLandmark);
                    List<Order> temList = new List<Order>();
                    /* foreach (Order order in orderList)
                     {
                         if (System.Object.ReferenceEquals(order.lendmark1, delLandmark) || System.Object.ReferenceEquals(order.lendmark2, delLandmark)) ;
                         {
                             temList.Add(order);
                         }
                     }

                     foreach (Order delOrder in temList)
                     {
                         orderList.Remove(delOrder);
                     }*/



                }

                localDiscoverdLandmark.Add(land);
                /* if (orderType != null)
                 {
                     Order order = new Order(orderType, land, land2);
                     orderList.Add(order);
                 }*/
                return true;





            }

            if (land.type == "Disjunctive")
            {
                Landmark delLandmark = null;
                bool flag = true;
                List<GroundedPredicate> dell = new List<GroundedPredicate>();
                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {
                    if (allPrivateLandmarks)
                    {
                        if (startState.m_lPredicates.Contains(fact.Key))
                            return false;
                    }
                    else
                    {
                        if (privateCanGet.Contains(fact.Key))
                            return false;
                    }
                    if (!flag) break;
                    foreach (Landmark tmp in localDiscoverdLandmark)
                    {
                        if (tmp.facts.ContainsKey(fact.Key))
                        {

                            dell.Add(fact.Key);
                            //delLandmark = tmp;
                            //flag = false;
                            //break;

                        }

                    }

                }
                foreach (GroundedPredicate d in dell)
                {
                    land.facts.Remove(d);
                }
                if (land.facts.Count == 0)
                    return false;
                if (flag)
                {
                    localDiscoverdLandmark.Add(land);
                    /*if (orderType != null)
                    {
                        Order order = new Order(orderType, land, land2);
                        orderList.Add(order);
                    }*/
                    return true;
                }
                else
                {
                    if (delLandmark.facts.Count > land.facts.Count)
                    {
                        localDiscoverdLandmark.Remove(delLandmark);
                        /*List<Order> temList = new List<Order>();
                        foreach (Order order in orderList)
                        {
                            if (System.Object.ReferenceEquals(order.lendmark1, delLandmark) || System.Object.ReferenceEquals(order.lendmark2, delLandmark))
                            {
                                temList.Add(order);
                            }


                        }

                        foreach (Order delOrder in temList)
                        {
                            orderList.Remove(delOrder);
                        }*/
                    }
                    else
                        return false;
                }
            }
            return false;
        }
        public void fullDetection()
        {
            privateCanGet = new HashSet<GroundedPredicate>();

            foreach (GroundedPredicate prop in startState.Predicates)
            {
                privateCanGet.Add(prop);
            }
        }
        public HashSet<GroundedPredicate> WhatICanGetWithMyPrivate()
        {
            privateCanGet = new HashSet<GroundedPredicate>();

            foreach (GroundedPredicate prop in startState.Predicates)
            {

                privateCanGet.Add(prop);
            }
            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;


                foreach (Action act in privateActions)
                {
                    if (Contains(privateCanGet, act.HashPrecondition))
                    {


                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!privateCanGet.Contains(addProp))
                                {

                                    privateCanGet.Add(addProp);

                                    flag2 = true;
                                }

                            }
                        }

                    }


                }



            }
            return privateCanGet;
        }

        public void ReduceLandmrkList(List<Landmark> newListOfLandmarks)
        {
            if (newListOfLandmarks != null)
                discoverdLandmark = newListOfLandmarks;

        }





        /* public bool ReachTheGoal()
         {
             WhatICanGetWithMyPrivate();
            

             foreach (GroundedPredicate gp in goal)
             {
                 if (!privateCanGet.Contains(gp))
                 {
                     return false; 
                 }
             }
             return true;

         }*/
        public void FindYourLandmarks(List<Landmark> Alllandmarks)
        {
            publicLandmarks = new List<Landmark>();
            //List<Landmark> dell = new List<Landmark>();
            foreach (Landmark l in Alllandmarks)
            {
                bool privateLand = false;
                bool cont = false;

                foreach (GroundedPredicate gp in l.facts.Keys)
                {
                    if (privateCanGet.Contains(gp))
                    {
                        cont = true;
                        break;
                    }
                }

                if (cont)
                    continue;

                foreach (Action act in m_actions)
                {
                    foreach (GroundedPredicate gp in l.facts.Keys)
                    {
                        if (act.HashEffects.Contains(gp))
                        {
                            privateLand = true;
                            if (!publicLandmarks.Contains(l))
                                publicLandmarks.Add(l);
                            //dell.Add(l);
                            break;
                        }
                    }
                    if (privateLand)
                        break;
                }
            }
            // foreach (Landmark dellLand in dell)
            {
                //    Alllandmarks.Remove(dellLand);
            }
        }
        public bool ReachTheGoal(int stateIndex)
        {

            // if (publicRelevantLandmark.Count > 0) return false;
           // StateInfo curentState = hashOfStates.ElementAt(stateIndex).Key;
            StateInfo curentState = mapToState[stateIndex]; 
            foreach (GroundedPredicate gp in goal)
            {
                if (!curentState.state.m_lPredicates.Contains(gp))
                {
                    return false;
                }
            }
            /*
            foreach (int index in indexOfGoals)
            {
                if (curentState.landmarksVector[index] == false)
                    return false;
            }*/
            return true;

        }


        public bool CanDo(int stateNumber, Action act)
        {
            // StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;
             //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;
            StateInfo oldState = mapToState[stateNumber]; 
            //StateInfo oldState = hashOfStates.FirstOrDefault(x => x.Value == stateNumber).Key;
            //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key;;
            return oldState.state.CanDo(act);
        }

        public void UpDateVectors(int stateNumber, bool[] landmark)
        {
            //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key; ;
            StateInfo oldState = mapToState[stateNumber]; 
            Array.Copy(landmark, oldState.landmarksVector, landmark.Length);
            oldState.landmarksVector = landmark;
            int i = 0;
            foreach (Order order in ReasonableOrdering)
            {
                if (landmark[order.lendmark1.index] == true)
                {
                    oldState.ReasonableOrdering[i] = true;
                }
                i++;
            }

        }
        public KeyValuePair<int, bool[][]> DemoApply(int stateNumber, Action act, out bool[] satisfiedNew, bool[] lVetor, bool[] oVector, HashSet<Predicate> lNewPublicPredicates)
        {
            if (act.agent == name)
            {
                // Agent StencilingAgent = new Agent(this);

                //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key; ;
                StateInfo oldState = mapToState[stateNumber]; 
                oldState.landmarksVector = new bool[lVetor.Length];
                oldState.ReasonableOrdering = new bool[oVector.Length];
                Array.Copy(lVetor, oldState.landmarksVector, lVetor.Length);
                Array.Copy(oVector, oldState.ReasonableOrdering, oVector.Length);


                //if (Contains(oldState.Key, act.HashEffects))
                //    return   new KeyValuePair<int, int>(-1, -1);

                bool[] newActionsVector = new bool[privateActions.Count];
                for (int i = 0; i < oldState.actionVector.Length; i++)
                {
                    newActionsVector[i] = oldState.actionVector[i];////
                }
              
                CompoundFormula eff;
                if (act.Effects is CompoundFormula)
                {
                    eff = (CompoundFormula)act.Effects;
                }
                else
                {
                    eff = new CompoundFormula("and");
                    eff.AddOperand(act.Effects);
                }
              //  State newState = oldState.state.ApplyFormulaEffectII(eff, MutuallyExclusive, PublicPredicates, canGetPredicate, newActionsVector, publicActions, act.HashPrecondition);
                State newState = oldState.state.ApplyEffectCf(act, MutuallyExclusive, act.HashPrecondition, PublicPredicates, canGetPredicate, newActionsVector, privateActions);

                //State newState = oldState.state.ApplyEffect(act, MutuallyExclusive, act.HashPrecondition);

                foreach (GroundedPredicate p in newState.Predicates)
                {
                    if (PublicPredicates.Contains(p))
                        lNewPublicPredicates.Add(p);
                }

                if (newState == null)
                {
                    throw new NotImplementedException();
                    //return new KeyValuePair<int, bool[]>(-1, null);
                }
                // StencilingAgent.aproximatePublicState.ApplyEffect(act,PublicPredicates);

                UpdateAproximtState(newState, newActionsVector);

                bool[] newPublicRelevantLandmarks = null;
                bool[] newReasonableOrdering = null;

                int notSatisfy = SatisfyLandmark(newState.m_lPredicates, oldState.landmarksVector, out newPublicRelevantLandmarks, oldState.ReasonableOrdering, out newReasonableOrdering, out satisfiedNew);



                StateInfo state = new StateInfo(newState, newPublicRelevantLandmarks, newActionsVector, newReasonableOrdering, satisfiedNew);
                //allStates.Add(state);
                int stateIndex = -1;
                if (!hashOfStates.ContainsKey(state))
                {
                    hashOfStates.Add(state, hashOfStates.Count);
                    mapToState.Add(hashOfStates.Count-1, state);
                    stateIndex = hashOfStates.Count - 1;
                }
                else
                {
                    stateIndex = hashOfStates[state];
                }
                double dis = FindDis(act);
                if (dis < 0)
                    dis = 0;
                else
                    dis = dis / 100.0;
                bool[][] ans = new bool[2][];
                ans[0] = new bool[newPublicRelevantLandmarks.Length];
                ans[1] = new bool[newReasonableOrdering.Length];
                Array.Copy(newPublicRelevantLandmarks, ans[0], newPublicRelevantLandmarks.Length);
                Array.Copy(newReasonableOrdering, ans[1], newReasonableOrdering.Length);
                return new KeyValuePair<int, bool[][]>(stateIndex, ans);
            }
            else
            {
                //Agent StencilingAgent = new Agent(this);
                //StateInfo oldState = hashOfStates.ElementAt(stateNumber).Key; ;
                StateInfo oldState = mapToState[stateNumber]; 
                oldState.landmarksVector = new bool[lVetor.Length];
                oldState.ReasonableOrdering = new bool[oVector.Length];
                Array.Copy(lVetor, oldState.landmarksVector, lVetor.Length);
                Array.Copy(oVector, oldState.ReasonableOrdering, oVector.Length);
                //State newState = oldState.state.ApplyEffect(act, PublicPredicates, MutuallyExclusive, act.HashPrecondition);
                bool[] newActionsVector = new bool[privateActions.Count];
                for (int i = 0; i < oldState.actionVector.Length; i++)
                {
                    newActionsVector[i] = oldState.actionVector[i];////
                }
                State newState = oldState.state.PassiveApplyEffectCF(act, MutuallyExclusive, act.HashPrecondition, PublicPredicates, canGetPredicate, newActionsVector, privateActions);

                //UpdateAproximtState(newState);
                bool[] newPublicRelevantLandmarks = null;
                /*int notSatisfy = 0;
                for (int i = 0; i < oldState.Value.Length; i++)
                {
                    if (!oldState.Value[i])
                        notSatisfy++;
                }*/

                bool[] newReasonableOrdering = null;
                bool relevantToMe = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    //if (PublicPredicates.Contains(gp) || PublicPredicates.Contains((GroundedPredicate)gp.Negate()))
                    if (!gp.Negation && PublicPredicates.Contains(gp))
                        relevantToMe = true;
                }
                if (relevantToMe)
                {
                    SatisfyLandmark(newState.m_lPredicates, oldState.landmarksVector, out newPublicRelevantLandmarks, oldState.ReasonableOrdering, out newReasonableOrdering, out satisfiedNew);
                }
                else
                {
                    newPublicRelevantLandmarks = oldState.landmarksVector;
                    newReasonableOrdering = oldState.ReasonableOrdering;
                    satisfiedNew = oldState.satisfiedNew;
                }
                /* {
                    newPublicRelevantLandmarks = new bool[oldState.landmarksVector.Length];
                    Array.Copy(oldState.landmarksVector, newPublicRelevantLandmarks, oldState.landmarksVector.Length);

                    newReasonableOrdering = new bool[oldState.ReasonableOrdering.Length];
                    Array.Copy(oldState.ReasonableOrdering, newReasonableOrdering, oldState.ReasonableOrdering.Length);

                    satisfiedNew = new bool[oldState.satisfiedNew.Length];
                    for (int i = 0; i < oldState.satisfiedNew.Length; i++)
                    {
                        satisfiedNew[i] = oldState.satisfiedNew[i];////
                    }

                }*/

                StateInfo state = new StateInfo(newState, newPublicRelevantLandmarks, oldState.actionVector, newReasonableOrdering, satisfiedNew);
                //allStates.Add(state);
                int stateIndex = -1;
                if (!hashOfStates.ContainsKey(state))
                {
                    hashOfStates.Add(state, hashOfStates.Count);
                    mapToState.Add(hashOfStates.Count-1, state);
                    stateIndex = hashOfStates.Count - 1;
                }
                else
                {
                    stateIndex = hashOfStates[state];
                }
                bool[][] ans = new bool[2][];
                ans[0] = new bool[newPublicRelevantLandmarks.Length];
                ans[1] = new bool[newReasonableOrdering.Length];
                Array.Copy(newPublicRelevantLandmarks, ans[0], newPublicRelevantLandmarks.Length);
                Array.Copy(newReasonableOrdering, ans[1], newReasonableOrdering.Length);

                return new KeyValuePair<int, bool[][]>(stateIndex, ans);



            }
        }
       
        public List<Order> FindReasonableOrdering(List<Agent> agents)
        {
            List<Order> ReasonableOrderList = new List<Order>();
            bool floog = false;
            int t = 0;
            foreach (Landmark land1 in publicRelevantLandmark)
            {
                if (!land1.isPublic)
                    continue;
                /*  bool stop=false;
                  foreach (Proposition fact in land1.facts.Keys)
                  {

                      if (problam.StartState.Contains(fact))
                      {
                          stop = true;
                          break;
                      }
                
                  }
                  if (stop)
                  {
                      continue;
                  }*/
                
                if (t == 16)
                    t = t;
                t++;
                if (land1.facts.Values.ElementAt(0) == "start")
                {
                    continue;
                }

                foreach (Landmark land2 in publicRelevantLandmark)
                {
                    if (!land2.isPublic)
                        continue;

                    if (land1.Equals(land2))
                    {
                        continue;
                    }
                    bool breakNow = false;
                    foreach (Order order in orderList)
                    {
                        if (order.lendmark1.Equals(land1) && order.lendmark2.Equals(land2))
                        {
                            breakNow = true;
                            break;
                        }
                    }
                    if (breakNow)
                        continue;

                    bool flag = false;
                    if (land2.GoalLandmark)
                        flag = true;
                    /* foreach (GroundedPredicate fact in land2.facts.Keys)
                     {
                         if (goal.Contains(fact))
                         {
                             flag = true;
                             break;
                         }
                     }*/

                    if (!flag)
                    {
                        HashSet<Landmark> firstLandmarkOrder = new HashSet<Landmark>();
                        bool again = true;
                        Queue<Landmark> q = new Queue<Landmark>();
                        q.Enqueue(land1);
                        while (q.Count != 0)
                        {
                            Landmark tempLandmark = q.Dequeue();
                            firstLandmarkOrder.Add(tempLandmark);

                            foreach (Order order in orderList)
                            {
                                if (order.lendmark1.Equals(tempLandmark))
                                {
                                    q.Enqueue(order.lendmark2);
                                }

                            }
                        }

                        firstLandmarkOrder.Remove(land1);
                        foreach (Order order in orderList)
                        {
                            if (order.lendmark1.Equals(land2) && firstLandmarkOrder.Contains(order.lendmark2))
                            {
                                flag = true;
                                break;
                            }
                        }

                    }


                    if (flag)
                    {
                        bool mutual = true;
                        //List<MutuallyExclusiveFacts> tmpMeflist = new List<MutuallyExclusiveFacts>();
                        foreach (GroundedPredicate fact1 in land1.facts.Keys)
                        {
                            HashSet<Predicate> localMutex = new HashSet<Predicate>();
                            if (MutuallyExclusive.ContainsKey(fact1))
                                localMutex = MutuallyExclusive[fact1];
                            foreach (GroundedPredicate fact2 in land2.facts.Keys)
                            {
                                if (!localMutex.Contains(fact2))
                                {
                                    mutual = false;
                                    break;
                                }
                            }
                            if (!mutual)
                                break;

                        }

                        if (!mutual)
                        {
                            HashSet<Landmark> landmarkList = new HashSet<Landmark>();
                            foreach (Order order in orderList)
                            {
                                if (order.lendmark2.Equals(land1))
                                {
                                    landmarkList.Add(order.lendmark1);
                                }
                            }

                            foreach (Landmark land in landmarkList)
                            {
                                mutual = true;
                                foreach (GroundedPredicate fact1 in land.facts.Keys)
                                {
                                    if (MutuallyExclusive.ContainsKey(fact1))
                                    {
                                        HashSet<Predicate> localMutex = MutuallyExclusive[fact1];
                                        foreach (GroundedPredicate fact2 in land2.facts.Keys)
                                        {

                                            if (!localMutex.Contains(fact2))
                                            {
                                                mutual = false;
                                                break;
                                            }
                                        }
                                    }
                                    else
                                    {
                                        mutual = false;
                                    }
                                    if (!mutual)
                                        break;


                                }
                                if (mutual)
                                    break;
                            }
                        }
                        if (!mutual)
                        {
                            List<Action> canGetFact = new List<Action>();
                            /* foreach (GroundedPredicate fact in land1.facts.Keys)
                             {
                                 if (allFactsWithActAchieve.ContainsKey(fact))
                                     canGetFact.AddRange(allFactsWithActAchieve[fact]);
                             }*/
                            if (land1.lAchievers == null)//|| canGetFact.Count==0)
                                break;
                            //canGetFact.AddRange(land1.lAchievers);
                            HashSet<GroundedPredicate> land2Mutex = GetMutex(land2);
                            foreach(Action act in land1.lAchievers)
                            {
                               bool save=true;
                                foreach(GroundedPredicate pre in act.HashPrecondition)
                                {
                                    if(land2Mutex.Contains(pre))
                                    {
                                        save=false;
                                        break;
                                    }

                                }
                                if(save)
                                    canGetFact.Add(act);
                                
                              

                            }
                            List<GroundedPredicate> sharedEffect = FindSharedEffect(canGetFact);
                            foreach (GroundedPredicate sEff in sharedEffect)
                            {
                                mutual = false;
                                HashSet<Predicate> localMutex = new HashSet<Predicate>();
                                localMutex.Add(sEff.Negate());
                                if (MutuallyExclusive.ContainsKey(sEff))
                                {
                                    foreach (GroundedPredicate gp in MutuallyExclusive[sEff])
                                    {
                                        localMutex.Add(gp);
                                    }
                                }
                                bool tmpFlag = true;
                                
                                foreach (GroundedPredicate fact2 in land2.facts.Keys)
                                {
                                    if (!localMutex.Contains(fact2))
                                    {
                                        tmpFlag = false;
                                        break;
                                    }
                                }
                                if (tmpFlag)
                                {
                                    mutual = true;
                                    break;
                                }
                            }
                        }
                        if (!mutual)
                        {
                           /* if (land2.facts.Keys.Count == 1)
                            {
                                foreach (Agent agent in agents)
                                {
                                    agent.SetLandmarkToExplorer(land1);
                                }


                                HashSet<GroundedPredicate> publicSet = new HashSet<GroundedPredicate>();

                                foreach (Agent agent in agents)
                                {
                                    HashSet<GroundedPredicate> tmp = agent.Detection();
                                    foreach (var gp in tmp)
                                    {
                                        if (!publicSet.Contains(gp))
                                        {
                                            publicSet.Add(gp);
                                        }
                                    }
                                }

                                bool flag2 = true;
                                while (flag2)
                                {
                                    flag2 = false;
                                    foreach (Agent agent in agents)
                                    {

                                        HashSet<GroundedPredicate> tmp = agent.WhatYoCanGet(publicSet);

                                        foreach (var gp in tmp)
                                        {
                                            if (!publicSet.Contains(gp))
                                            {
                                                publicSet.Add(gp);
                                                flag2 = true;
                                            }
                                        }
                                    }

                                }
                                foreach (Agent agent in agents)
                                {
                                    agent.UpDateWhatICanGet(land2);
                                }
                                flag2 = true;
                                while (flag2)
                                {
                                    flag2 = false;
                                    foreach (Agent agent in agents)
                                    {

                                        HashSet<GroundedPredicate> tmp = agent.WhatYoCanGet(publicSet);

                                        foreach (var gp in tmp)
                                        {
                                            if (!publicSet.Contains(gp))
                                            {
                                                publicSet.Add(gp);
                                                flag2 = true;
                                            }
                                        }
                                    }

                                }
                                mutual = true;
                                foreach (GroundedPredicate fact in land1.facts.Keys)
                                {
                                    if (publicSet.Contains(fact))
                                    {
                                        mutual = false;
                                        break;
                                    }
                                }
                            }*/
                        }
                        if (mutual)
                        {
                            Order order = new Order("Reasonable", land1, land2);

                            ReasonableOrderList.Add(order);
                            //  if (floog)
                            // {
                            // floog = floog;

                            // Console.WriteLine(land1.facts.Keys.ElementAt(0).ToString() + " ---> " + land2.facts.Keys.ElementAt(0).ToString() + '\n');


                            // }
                        }
                        //if (floog)
                        //{
                        //    Console.WriteLine("");
                        //    Console.WriteLine("");
                        //}
                    }


                }

            }
            List<Order> temp = new List<Order>();
            foreach (Order order in ReasonableOrderList)
            {
                if (order.lendmark1.facts.ElementAt(0).Value != "start" && !order.lendmark1.Equals(order.lendmark2))
                    temp.Add(order);

            }

            ReasonableOrderList = temp;

            return ReasonableOrderList;

        }
        public HashSet<GroundedPredicate> GetMutex(Landmark land2)
        {
            bool flag4 = true;
            HashSet<GroundedPredicate> localMutex2 = new HashSet<GroundedPredicate>();
            int steps = 0;
            foreach (GroundedPredicate gp in land2.facts.Keys)
            {
                if (MutuallyExclusive.ContainsKey(gp))
                {
                    if (steps == 0)
                    {
                        foreach (GroundedPredicate m in MutuallyExclusive[gp])
                        {
                            localMutex2.Add(m);
                        }
                    }
                    else
                    {
                        HashSet<GroundedPredicate> tmp = new HashSet<GroundedPredicate>();
                        foreach (GroundedPredicate m in MutuallyExclusive[gp])
                        {
                            if (localMutex2.Contains(m))
                            {
                                tmp.Add(m);
                            }
                        }
                        localMutex2 = tmp;
                    }


                }
                steps++;
            }
            return localMutex2;
        }
        public static List<string> ReadPlan(string sPath)
        {
            List<string> lPlan = new List<string>();
            string sPlanFile = "plan.txt";
            if (File.Exists(sPath + sPlanFile))
            {
                StreamReader sr = new StreamReader(sPath + sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if (sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "mipsSolution.soln"))
            {
                StreamReader sr = new StreamReader(sPath + "mipsSolution.soln");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        int iEnd = sLine.IndexOf(")");
                        sLine = sLine.Substring(iStart + 1, iEnd - iStart - 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else
            {
                /*
                if (SDRPlanner.AddTagRefutationToGoal)
                {
                    SDRPlanner.AddTagRefutationToGoal = false;
                    lPlan = Plan(sPath, pssCurrent, out sChosen);
                }
                else
                 * */

                //throw new Exception("ended");

                return null;
            }

            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }
        public int MergeLandmarks(Landmark publicLanmark)
        {

            int count = 0;
            foreach (Landmark l2 in localDiscoverdLandmark)
            {
                Landmark l3 = new Landmark("Disjunctive", publicLanmark.GoalLandmark || l2.GoalLandmark);
                foreach (var fact in publicLanmark.facts)
                {
                    l3.AddFact(fact.Key, fact.Value);
                }

                foreach (var fact in l2.facts)
                {
                    if (!l3.facts.ContainsKey(fact.Key))
                        l3.AddFact(fact.Key, fact.Value);
                }

                bool flg = InserLandmark(l3, null, null);
                if (flg)
                {
                    publicLandmarks.Add(l3);
                    count++;
                }
            }
            return count;


        }
        private bool Contains(HashSet<GroundedPredicate> x, HashSet<GroundedPredicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
        private bool Contains(List<GroundedPredicate> x, List<GroundedPredicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
        private bool Contains(HashSet<GroundedPredicate> x, List<Predicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) 
                    return false;
            }
            return true;
        }
        private bool Contains(HashSet<GroundedPredicate> x, List<GroundedPredicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
        private bool Contains(State x, List<Predicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.m_lPredicates.Contains(gP)) return false;
            }
            return true;
        }
        private int SatisfyLandmarkNew(HashSet<Predicate> newState, bool[] landmarks, out bool[] notSatisfiedLandmarks, bool[] reasonableOrderingVector, out bool[] outReasonableOrdering, out bool[] satisfiedNew)
        {
            outReasonableOrdering = new bool[reasonableOrderingVector.Length];
            Array.Copy(reasonableOrderingVector, outReasonableOrdering, reasonableOrderingVector.Length);
            int notSatisfied = 0;
            bool f = false;
            notSatisfiedLandmarks = new bool[landmarks.Length];
            satisfiedNew = new bool[landmarks.Length];
            for (int i = 0; i < landmarks.Length; i++)
            {
                f = false;
                if (landmarks[i] == false)
                {
                    foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                    {
                        if (newState.Contains(fact))
                        {
                            notSatisfiedLandmarks[i] = true;
                            satisfiedNew[i] = true;
                            f = true;
                            /* for (int k = 0; k < outReasonableOrdering.Length; k++)
                             {
                                 if (outReasonableOrdering[k] == false && ReasonableOrdering[k].lendmark1.Equals(publicRelevantLandmark[i]))
                                 {
                                     outReasonableOrdering[k] = true;
                                 }
                             }*/
                            break;
                        }

                    }

                    if (!f)
                    {
                        notSatisfiedLandmarks[i] = false;
                        notSatisfied += publicRelevantLandmark[i].worth;
                    }
                }
                else
                {
                    //if (publicRelevantLandmark[i].facts.ElementAt(0).Value.Equals("Goal"))
                    if (publicRelevantLandmark[i].GoalLandmark)
                    {
                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                        {
                            if (newState.Contains(fact))
                            {
                                notSatisfiedLandmarks[i] = true;
                                satisfiedNew[i] = true;
                                f = true;
                                break;
                            }

                        }

                        if (!f)
                        {

                            notSatisfiedLandmarks[i] = false;
                            notSatisfied += publicRelevantLandmark[i].worth;
                        }

                    }
                    else
                    {
                        notSatisfiedLandmarks[i] = true;
                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                        {
                            if (newState.Contains(fact))
                            {
                                satisfiedNew[i] = true;
                                break;
                            }
                        }
                    }



                }
            }

            bool agein = true;
            while (agein)
            {
                agein = false;
                for (int i = 0; i < notSatisfiedLandmarks.Length; i++)
                {
                    f = false;
                    if (notSatisfiedLandmarks[i] == true)
                    {


                        /*   foreach (Order order in orderList)
                           {
                              // if(order.lendmark1.ToString().Equals(Domain.FALSE_PREDICATE) )
                                  // continue;
                               if (order.lendmark1.Equals(publicRelevantLandmark[i]))
                               {
                                   int index = order.lendmark2.index;
                                   if (index > -1)
                                   {
                                       if (notSatisfiedLandmarks[index] == false)
                                       {
                                           foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                                           {
                                               if (newState.Contains(fact))
                                               {
                                                   notSatisfiedLandmarks[i] = true;
                                                   f = true;
                                                   break;
                                               }

                                           }

                                           if (!f)
                                           {
                                               notSatisfiedLandmarks[i] = false;
                                               notSatisfied += publicRelevantLandmark[i].worth;
                                               agein = true;
                                               break;
                                           }
                                       }
                                   }

                               }
                           }*/
                        int counter = 0;
                        foreach (Order order in ReasonableOrdering)
                        {
                            if (outReasonableOrdering[counter] == false)
                            {
                                if (order.lendmark2.Equals(publicRelevantLandmark[i]))
                                {
                                    int index = order.lendmark1.index;
                                    if (notSatisfiedLandmarks[index] == false)
                                    {
                                        notSatisfiedLandmarks[i] = false;
                                        notSatisfied += publicRelevantLandmark[i].worth;
                                        agein = true;
                                        break;
                                    }
                                }
                            }
                            counter++;
                        }

                    }

                }
            }

            for (int i = 0; i < landmarks.Length; i++)
            {
                f = false;
                if (landmarks[i] == false && notSatisfiedLandmarks[i] == true)
                {
                    for (int k = 0; k < outReasonableOrdering.Length; k++)
                    {
                        if (outReasonableOrdering[k] == false && ReasonableOrdering[k].lendmark1.Equals(publicRelevantLandmark[i]))
                        {
                            outReasonableOrdering[k] = true;
                        }
                    }
                }

            }
            return notSatisfied;
        }
        private int SatisfyLandmark(HashSet<Predicate> newState, bool[] landmarks, out bool[] notSatisfiedLandmarks, bool[] reasonableOrderingVector, out bool[] outReasonableOrdering, out bool[] satisfiedNew)
        {
            outReasonableOrdering = new bool[reasonableOrderingVector.Length];
            Array.Copy(reasonableOrderingVector, outReasonableOrdering, reasonableOrderingVector.Length);
            int notSatisfied = 0;
            bool f = false;
            notSatisfiedLandmarks = new bool[landmarks.Length];
            satisfiedNew = new bool[landmarks.Length];
            for (int i = 0; i < landmarks.Length; i++)
            {
                f = false;
                if (landmarks[i] == false)
                {
                    foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                    {
                        if (newState.Contains(fact))
                        {
                            notSatisfiedLandmarks[i] = true;
                            satisfiedNew[i] = true;
                            f = true;
                            for (int k = 0; k < outReasonableOrdering.Length; k++)
                            {
                                if (outReasonableOrdering[k] == false && ReasonableOrdering[k].lendmark1.Equals(publicRelevantLandmark[i]))
                                {
                                    outReasonableOrdering[k] = true;
                                }
                            }
                            break;
                        }

                    }

                    if (!f)
                    {
                        notSatisfiedLandmarks[i] = false;
                        notSatisfied += publicRelevantLandmark[i].worth;
                    }
                }
                else
                {
                    //if (publicRelevantLandmark[i].facts.ElementAt(0).Value.Equals("Goal"))
                    if (publicRelevantLandmark[i].GoalLandmark)
                    {
                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                        {
                            if (newState.Contains(fact))
                            {
                                notSatisfiedLandmarks[i] = true;
                                satisfiedNew[i] = true;
                                f = true;
                                break;
                            }

                        }

                        if (!f)
                        {

                            notSatisfiedLandmarks[i] = false;
                            notSatisfied += publicRelevantLandmark[i].worth;
                        }

                    }
                    else
                    {
                        notSatisfiedLandmarks[i] = true;
                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                        {
                            if (newState.Contains(fact))
                            {
                                satisfiedNew[i] = true;
                                break;
                            }
                        }
                    }



                }
            }

            bool agein = true;
            while (agein)
            {
                agein = false;
                for (int i = 0; i < notSatisfiedLandmarks.Length; i++)
                {
                    f = false;
                    if (notSatisfiedLandmarks[i] == true)
                    {


                        /*   foreach (Order order in orderList)
                           {
                              // if(order.lendmark1.ToString().Equals(Domain.FALSE_PREDICATE) )
                                  // continue;
                               if (order.lendmark1.Equals(publicRelevantLandmark[i]))
                               {
                                   int index = order.lendmark2.index;
                                   if (index > -1)
                                   {
                                       if (notSatisfiedLandmarks[index] == false)
                                       {
                                           foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                                           {
                                               if (newState.Contains(fact))
                                               {
                                                   notSatisfiedLandmarks[i] = true;
                                                   f = true;
                                                   break;
                                               }

                                           }

                                           if (!f)
                                           {
                                               notSatisfiedLandmarks[i] = false;
                                               notSatisfied += publicRelevantLandmark[i].worth;
                                               agein = true;
                                               break;
                                           }
                                       }
                                   }

                               }
                           }*/
                        int counter = 0;
                        foreach (Order order in ReasonableOrdering)
                        {
                            if (outReasonableOrdering[counter] == false)
                            {
                                if (order.lendmark2.Equals(publicRelevantLandmark[i]))
                                {
                                    int index = order.lendmark1.index;
                                    if (notSatisfiedLandmarks[index] == false)
                                    {
                                        notSatisfiedLandmarks[i] = false;
                                        notSatisfied += publicRelevantLandmark[i].worth;
                                        agein = true;
                                        break;
                                    }
                                }
                            }
                            counter++;
                        }

                    }

                }
            }
            return notSatisfied;
        }
        private void FillFactDictionary(out Dictionary<Predicate, List<Action>> facts)
        {


            facts = new Dictionary<Predicate, List<Action>>();
            foreach (Action act in m_actions)
            {
                if (act.Effects != null)
                {
                    foreach (GroundedPredicate prop1 in act.HashEffects)
                    {
                        if (!facts.ContainsKey(prop1))
                        {
                            List<Action> templist = new List<Action>();
                            templist.Add(act);
                            facts.Add(prop1, templist);

                        }

                        else
                        {
                            facts[prop1].Add(act);
                        }


                    }
                }



            }
        }
        public List<GroundedPredicate> FindSharedEffect(List<Action> actions)
        {
            List<GroundedPredicate> sharedEffect = new List<GroundedPredicate>();
            if (actions.Count > 0)
            {
                Action firstAct = actions[0];
                actions.RemoveAt(0);

                foreach (GroundedPredicate eff in firstAct.HashEffects)
                {
                    bool shared = true;
                    foreach (Action act in actions)
                    {
                        if (!act.HashEffects.Contains(eff))
                        {
                            shared = false;
                            break;
                        }
                    }
                    if (shared)
                        sharedEffect.Add(eff);

                }

            }
            return sharedEffect;
        }
    }
}
