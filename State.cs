using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace Planning
{
    public class State
    {
        public IEnumerable<Predicate> Predicates { get { return m_lPredicates; } }
        public State prev = null;
        public Action actToArrive = null;
        public int m_disFromStart = 0;
        public int m_heuristic;
        public int code = -1;
        public HashSet<Predicate> m_lPredicates;
        public List<Action> AvailableActions { get; protected set; }
        private State m_sPredecessor;
        public bool MaintainNegations { get; private set; }
        public Problem Problem { get;  set; }
        public int ID { get; private set; }
        public Dictionary<string, double> FunctionValues { get; private set; }
        public int Time { get; private set; }

        public static int STATE_COUNT = 0;

        public State()
        {

        }
        public State(Problem p)
        {
            Problem = p;
            m_sPredecessor = null;
            m_lPredicates = new HashSet<Predicate>();
            AvailableActions = new List<Action>();
            MaintainNegations = true;
            ID = STATE_COUNT++;
            FunctionValues = new Dictionary<string, double>();
            Time = 0;
            if (p != null)
            {
                foreach (string sFunction in Problem.Domain.Functions)
                {
                    FunctionValues[sFunction] = 0.0;
                }
            }
        }

        public State(State sPredecessor)
            : this(sPredecessor.Problem)
        {
            m_sPredecessor = sPredecessor;
            m_lPredicates = new HashSet<Predicate>(sPredecessor.Predicates);
            FunctionValues = new Dictionary<string, double>();
            if (sPredecessor == null || sPredecessor.FunctionValues == null)
                FunctionValues = new Dictionary<string, double>();
            else
            {
                foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                    FunctionValues[p.Key] = p.Value;
            }
            Time = sPredecessor.Time + 1;
            MaintainNegations = sPredecessor.MaintainNegations;
            
        }
        
        
        public bool ConsistentWith(Predicate p)
        {
            foreach (Predicate pState in Predicates)
            {
                if (!p.ConsistentWith(pState))
                    return false;
            }
            return true;
        }

        public bool ConsistentWith(Formula f)
        {
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f;
                bool bConsistent = false;
                foreach (Formula fOperand in cf.Operands)
                {
                    bConsistent = ConsistentWith(fOperand);
                    if (cf.Operator == "and" && !bConsistent)
                        return false;
                    if (cf.Operator == "or" && bConsistent)
                        return true;
                    if (cf.Operator == "not")
                        return !bConsistent;
                }
                if (cf.Operator == "and")
                    return true;
                if (cf.Operator == "or")
                    return false;
            }
            else
            {
                PredicateFormula vf = (PredicateFormula)f;
                return ConsistentWith(vf.Predicate);
            }
            return false;
        }
        public void AddPredicate(Predicate p)
        {
            if (m_lPredicates.Contains(p))
                return;
            /*
            foreach (Predicate pState in Predicates)
            {
                if (pState.Equals(p))
                    return;
            }
             * */
            m_lPredicates.Add(p);

        }

        public override bool Equals(object obj)
        {
           // return (GetHashCode() == ((State)obj).GetHashCode());
            if (obj is State)
            {
                State s = (State)obj;
                if (s.m_lPredicates.Count != m_lPredicates.Count)
                    return false;
                
                foreach (Predicate p in s.Predicates)
                    if (!Predicates.Contains(p))
                        return false;
                return true;
                 
                //return m_lPredicates.Equals(s.m_lPredicates);
            }
            return false;
        }
        public virtual void GroundAllActions()
        {
            AvailableActions = Problem.Domain.GroundAllActions(m_lPredicates, MaintainNegations);
        }
        public bool Contains(Formula f)
        {
            return f.ContainedIn(m_lPredicates, false);
        }
        public virtual State Clone()
        {
            return new State(this);
        }
        /*
        public State Apply(string sActionName)
        {
            sActionName = sActionName.Replace(' ', '_');//moving from ff format to local format
            if (AvailableActions.Count == 0)
                GroundAllActions(Problem.Domain.Actions);
            foreach (Action a in AvailableActions)
                if (a.Name == sActionName)
                    return Apply(a);
            return null;
        }
         * */
        public State Apply(string sActionName)
        {
            //Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '), m_lPredicates, false);
            Action a=null;
            if (Problem!=null && Problem.Domain.mapActionNameToAction != null)
            {
                if (Problem.Domain.mapActionNameToAction.ContainsKey(sActionName))
                {
                    a = Problem.Domain.mapActionNameToAction[sActionName];
                }
            }
            else
            {
                string sOutputName = Domain.MapGroundedActionNamesToOutputNames[sActionName];
                sOutputName = sOutputName.Substring(1, sOutputName.Length - 2);
                a = Problem.Domain.GroundActionByName(sOutputName.Split(' '), m_lPredicates, false);
            }
            if (a == null)
                return null;
            return ApplyII(a);
        }
        public State Apply(string sActionName,Domain d)
        {
            //Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '), m_lPredicates, false);
            Action a = null;
           
            {
                string sOutputName = Domain.MapGroundedActionNamesToOutputNames[sActionName];
                sOutputName = sOutputName.Substring(1, sOutputName.Length - 2);
                a = d.GroundActionByName(sOutputName.Split(' '), m_lPredicates, false);
            }
            if (a == null)
                return null;
            return ApplyII(a);
        }
        public bool CanDo(Action a)
        {
            //return (a.Preconditions.IsTrue(m_lPredicates, MaintainNegations));
            /*HashSet<GroundedPredicate> pos = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in m_lPredicates)
            {
                if (!gp.Negation)
                    pos.Add(gp);
            }*/
            return m_lPredicates.IsSupersetOf(a.HashPrecondition);
        }

        public State Apply(Action a)
        {
            //Debug.WriteLine("Executing " + a.Name);
            if (a is ParametrizedAction)
                return null;
            if (a.Preconditions != null && !a.Preconditions.IsTrue(m_lPredicates, MaintainNegations))
                return null;

            State sNew = Clone();
            sNew.Time = Time + 1;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {
                /*
                if (a.HasConditionalEffects)
                {
                    sNew.AddEffects(a.GetApplicableEffects(m_lPredicates, MaintainNegations));
                }
                else
                {
                    sNew.AddEffects(a.Effects);
                }
                 * */
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (Predicate p in lDeleteList)
                    sNew.AddEffect(p);
                foreach (Predicate p in lAddList)
                    sNew.AddEffect(p);
                //sNew.AddEffects(a.Effects);
            }
            if (!MaintainNegations)
                sNew.RemoveNegativePredicates();
            if (sNew.Predicates.Contains(new GroundedPredicate(Domain.FALSE_PREDICATE)))
                Debug.WriteLine("BUGBUG");
            return sNew;
        }
        public State FullApplyEffect(Action a)
        {
            //Debug.WriteLine("Executing " + a.Name);
            if (a is ParametrizedAction)
                return null;
            

            State sNew = Clone();
            sNew.Time = Time + 1;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {
                /*
                if (a.HasConditionalEffects)
                {
                    sNew.AddEffects(a.GetApplicableEffects(m_lPredicates, MaintainNegations));
                }
                else
                {
                    sNew.AddEffects(a.Effects);
                }
                 * */
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (Predicate p in lDeleteList)
                    sNew.AddEffect(p);
                foreach (Predicate p in lAddList)
                    sNew.AddEffect(p);
                //sNew.AddEffects(a.Effects);
            }
            if (!MaintainNegations)
                sNew.RemoveNegativePredicates();
            if (sNew.Predicates.Contains(new GroundedPredicate(Domain.FALSE_PREDICATE)))
                Debug.WriteLine("BUGBUG");
            return sNew;
        }

        public State ApplyII(Action a)
        {
            if (a.Preconditions != null && !a.Preconditions.IsTrue(m_lPredicates, MaintainNegations))
                return null;
            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (GroundedPredicate p in lDeleteList)
                {
                    sNew.AddEffectII(p);

                }
                foreach (GroundedPredicate p in lAddList)
                {
                    sNew.AddEffectII(p);
                }

            }
            return sNew;
        }


        public State ApplyIII(Action a)
        {
            if (a.HashPrecondition != null )
            {
                foreach (GroundedPredicate pre in a.HashPrecondition)
                {
                    if(!m_lPredicates.Contains(pre))
                        return null;
                }              
            }
            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.HashEffects == null)
                return sNew;

            if (a.HashEffects != null)
            {
                foreach (GroundedPredicate p in a.HashEffects)
                {
                    sNew.AddEffectII(p);
                }                
            }

            return sNew;
        }
        public bool CanDone(Action a)
        {
            if (a.HashPrecondition != null)
            {
                foreach (GroundedPredicate pre in a.HashPrecondition)
                {
                    if (!m_lPredicates.Contains(pre))
                        return false;
                }
            }
            return true;
        }

        public State ApplyEffect(Action a,HashSet<GroundedPredicate> relevatPredicates)
        {
           

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {
                
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (GroundedPredicate p in lDeleteList)
                {
                    if (relevatPredicates.Contains((GroundedPredicate)p.Negate()))
                    {

                        sNew.AddEffectII(p);
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
                    if (relevatPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                    }

                }
                
            }
            
            return sNew;
        }
        public State ApplyEffect(Formula eff, HashSet<GroundedPredicate> relevatPredicates)
        {


            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (eff == null)
                return sNew;

            if (eff != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(eff, lAddList, lDeleteList);
                foreach (GroundedPredicate p in lDeleteList)
                {
                    if (relevatPredicates.Contains((GroundedPredicate)p.Negate()))
                    {

                        sNew.AddEffectII(p);
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
                    if (relevatPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                    }

                }

            }

            return sNew;
        }
        public State ApplyEffect(Action a, HashSet<GroundedPredicate> relevatPredicates, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre)
        {


            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
               /* List<Predicate> dell = new List<Predicate>();
                foreach (Predicate oldP in sNew.m_lPredicates)
                {
                    bool l = false;
                    if (!mutex.ContainsKey(oldP))
                        continue;
                    HashSet<Predicate> localMutex = mutex[oldP];
                    foreach (GroundedPredicate p in lAddList)
                    {

                        if (localMutex.Contains(p))
                        {
                            dell.Add(oldP);
                            l = true;
                            break;
                        }
                    }
                    if (l) continue;
                   /* foreach (GroundedPredicate p in pre)
                    {

                        if (localMutex.Contains(p))
                        {
                            dell.Add(oldP);
                            l = true;
                            break;
                        }
                    }*/


               // }
               // foreach (Predicate pdell in dell)
                //    sNew.m_lPredicates.Remove(pdell);
                foreach (GroundedPredicate p in lDeleteList)
                {
                    if (relevatPredicates.Contains((GroundedPredicate)p.Negate()))
                    {

                        sNew.AddEffectII(p);
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
                    if (relevatPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                    }

                }

            }

            return sNew;
        }
        public State ApplyEffect(Action a)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (GroundedPredicate p in lDeleteList)
                {
                   

                        sNew.AddEffectII(p);
                    
                }
                
                foreach (GroundedPredicate p in lAddList)
                {
                   
                        sNew.AddEffectII(p);

                        

                }
                

            }

            return sNew;
        }
        public State ApplyEffect(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet,bool[] actionVector,List<Action> privateActions)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {
               
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet = new HashSet<Predicate>();
                foreach (GroundedPredicate p in lAddList)
                {
                     if (!mutex.ContainsKey(p))
                        continue;
                     foreach (Predicate mp in mutex[p])
                     {
                         if(!mutexSet.Contains(mp))
                            mutexSet.Add(mp);
                     }
                }
                foreach (GroundedPredicate p in pre)
                {
                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet.Contains(mp))
                            mutexSet.Add(mp);
                    }
                }

                foreach (Predicate oldP in sNew.m_lPredicates)
                {
                 
                    
                            if (mutexSet.Contains(oldP))
                            {
                                dell.Add(oldP);
                                
                                
                            }
                     
                    }


                
                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    if(canGet.ContainsKey(pdell))
                    {
                        foreach(Action act in canGet[pdell])
                        {
                            actionVector[act.index] = false;
                         //   actionVector[privateActions.IndexOf(act)] = false;
                        }
                    }
                }
                
                foreach (GroundedPredicate p in lDeleteList)
                {


                    sNew.AddEffectII(p);

                }
                
                foreach (GroundedPredicate p in lAddList)
                {

                    sNew.AddEffectII(p);



                }
               

            }

            return sNew;
        }
        public State ApplyEffectCf(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, bool[] actionVector, List<Action> privateActions)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet = new HashSet<Predicate>();
                foreach (GroundedPredicate p in lAddList)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet.Contains(mp))
                                mutexSet.Add(mp);
                        }
                    }
                }
                foreach (GroundedPredicate p in pre)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet.Contains(mp))
                                mutexSet.Add(mp);
                        }
                    }
                }

                foreach (Predicate oldP in sNew.m_lPredicates)
                {
                    if (mutexSet.Contains(oldP))
                    {
                        dell.Add(oldP);
                    }

                }



                foreach (GroundedPredicate pdell in dell)
                {
                    
                    sNew.m_lPredicates.Remove(pdell);
                    if (canGet.ContainsKey(pdell))
                    {
                        foreach (Action act in canGet[pdell])
                        {
                            if (actionVector[act.index])
                                actionVector[act.index] = false;
                            
                        }
                    }
                }

                foreach (GroundedPredicate p in lDeleteList)
                {
                   // if (PublicPredicates.Contains((GroundedPredicate)p.Negate()))
                     //   sNew.AddEffectII(p);

                    GroundedPredicate tmp=(GroundedPredicate)p.Negate();
                        sNew.AddEffectII(p);
                        if (canGet.ContainsKey(tmp))
                        {
                            foreach (Action act in canGet[tmp])
                            {
                                if(actionVector[act.index])
                                 actionVector[act.index] = false;
                                   //actionVector[privateActions.IndexOf(act)] = false;
                            }
                        }
                }

                foreach (GroundedPredicate p in lAddList)
                {
                    sNew.AddEffectII(p);
                }


            }

            return sNew;
        }
        public State PassiveApplyEffect(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, bool[] actionVector, List<Action> privateActions)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet1 = new HashSet<Predicate>();
                HashSet<Predicate> mutexSet2 = new HashSet<Predicate>();
                foreach (GroundedPredicate p in lAddList)
                {
                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet1.Contains(mp))
                            mutexSet1.Add(mp);
                    }
                }
                foreach (GroundedPredicate p in pre)
                {
                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet2.Contains(mp))
                            mutexSet2.Add(mp);
                    }
                } 

                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet1.Contains(oldP))
                    {
                        dell.Add(oldP);
                    }
                    else
                    {
                        if (mutexSet2.Contains(oldP))
                        {
                            dell.Add(oldP);
                        }
                    }

                }



                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    if (canGet.ContainsKey(pdell))
                    {
                        foreach (Action act in canGet[pdell])
                        {
                            actionVector[act.index] = false;
                            //   actionVector[privateActions.IndexOf(act)] = false;
                        }
                    }
                }

               
                foreach (GroundedPredicate p in lDeleteList)
                {
                    if (PublicPredicates.Contains((GroundedPredicate)p.Negate()))
                    {

                        sNew.AddEffectII(p);
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
               //     if (PublicPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                    }

                }

            }

            return sNew;
        }
        public State PassiveApplyEffectCF(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, bool[] actionVector, List<Action> privateActions)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet1 = new HashSet<Predicate>();
                HashSet<Predicate> mutexSet2 = new HashSet<Predicate>();
                foreach (GroundedPredicate p in lAddList)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet1.Contains(mp))
                                mutexSet1.Add(mp);
                        }
                    }
                }


                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet1.Contains(oldP))
                    {
                        dell.Add(oldP);
                    }
                    else
                    {
                        if (mutexSet2.Contains(oldP))
                        {
                            dell.Add(oldP);
                        }
                    }

                }



                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    if (canGet.ContainsKey(pdell))
                    {
                        foreach (Action act in canGet[pdell])
                        {
                            actionVector[act.index] = false;
                            //   actionVector[privateActions.IndexOf(act)] = false;
                        }
                    }
                }


                foreach (GroundedPredicate p in lDeleteList)
                {
                    GroundedPredicate nGp = (GroundedPredicate)p.Negate();
                    if (PublicPredicates.Contains(nGp))
                    {

                        sNew.AddEffectII(p);
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
                  if (PublicPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                    }

                }

            }

            return sNew;
        }
        public State ApplyEffect(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, List<Action> privateActions)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet = new HashSet<Predicate>();
                foreach (GroundedPredicate p in lAddList)
                {
                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet.Contains(mp))
                            mutexSet.Add(mp);
                    }
                }
                foreach (GroundedPredicate p in pre)
                {
                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet.Contains(mp))
                            mutexSet.Add(mp);
                    }
                }

                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet.Contains(oldP))
                    {
                        dell.Add(oldP);


                    }

                }



              

                foreach (GroundedPredicate p in lDeleteList)
                {


                    sNew.AddEffectII(p);

                }

                foreach (GroundedPredicate p in lAddList)
                {

                    sNew.AddEffectII(p);



                }


            }

            return sNew;
        }
        public State ApplyEffect(Action a, Dictionary<Predicate, HashSet<Predicate>> mutex, List<Predicate> pre)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                foreach (Predicate oldP in sNew.m_lPredicates)
                {
                    bool l = false;
                    if (!mutex.ContainsKey(oldP))
                        continue;
                    HashSet<Predicate> localMutex = mutex[oldP];
                    foreach (GroundedPredicate p in lAddList)
                    {

                        if (localMutex.Contains(p))
                        {
                            dell.Add(oldP);
                            l = true;
                            break;
                        }
                    }
                    if (l) continue;
                    foreach (GroundedPredicate p in pre)
                    {

                        if (localMutex.Contains(p))
                        {
                            dell.Add(oldP);
                            l = true;
                            break;
                        }
                    }


                }
                foreach (Predicate pdell in dell)
                    sNew.m_lPredicates.Remove(pdell);

                foreach (GroundedPredicate p in lDeleteList)
                {


                    sNew.AddEffectII(p);

                }

                foreach (GroundedPredicate p in lAddList)
                {

                    sNew.AddEffectII(p);



                }


            }

            return sNew;
        }
        private void AddEffectII(Predicate pEffect)
        {
            if (!(pEffect is GroundedFunctionPredicate))
            {
                Predicate pNegateEffect = pEffect.Negate();
                if (m_lPredicates.Contains(pNegateEffect))
                {
                    //Debug.WriteLine("Removing " + pNegateEffect);
                    m_lPredicates.Remove(pNegateEffect);
                }
                /*
                if (!pEffect.Negation)
                {
                    //Debug.WriteLine("Adding " + pEffect);
                    m_lPredicates.Add(pEffect);
                }
                 * */
                if (!m_lPredicates.Contains(pEffect))
                {
                    m_lPredicates.Add(pEffect);//we are maintaining complete state information
                }
            }

        }
        private void AddEffect(Predicate pEffect)
        {
            if (Problem.Domain.IsFunctionExpression(pEffect.Name))
            {
                return;
                GroundedPredicate gpIncreaseDecrease = (GroundedPredicate)pEffect;
                double dPreviousValue = m_sPredecessor.FunctionValues[gpIncreaseDecrease.Constants[0].Name];
                double dDiff = double.Parse(gpIncreaseDecrease.Constants[1].Name);
                double dNewValue = double.NaN;
                if (gpIncreaseDecrease.Name.ToLower() == "increase")
                    dNewValue = dPreviousValue + dDiff;
                else if (gpIncreaseDecrease.Name.ToLower() == "decrease")
                    dNewValue = dPreviousValue + dDiff;
                else
                    throw new NotImplementedException();
                FunctionValues[gpIncreaseDecrease.Constants[0].Name] = dNewValue;
            } 
            else if (!m_lPredicates.Contains(pEffect))
            {
                Predicate pNegateEffect = pEffect.Negate();
                if (m_lPredicates.Contains(pNegateEffect))
                {
                    //Debug.WriteLine("Removing " + pNegateEffect);
                    m_lPredicates.Remove(pNegateEffect);
                }
                /*
                if (!pEffect.Negation)
                {
                    //Debug.WriteLine("Adding " + pEffect);
                    m_lPredicates.Add(pEffect);
                }
                 * */
                m_lPredicates.Add(pEffect);//we are maintaining complete state information
            }
        }
        private void AddEffects(Formula fEffects)
        {
            if (fEffects is PredicateFormula)
            {
                AddEffect(((PredicateFormula)fEffects).Predicate);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof" || cf.Operator == "or")//BUGBUG - should treat or differently
                {
                    int iRandomIdx = RandomGenerator.Next(cf.Operands.Count);
                    AddEffects(cf.Operands[iRandomIdx]);
                    GroundedPredicate pChoice = new GroundedPredicate("Choice");
                    pChoice.AddConstant(new Constant("ActionIndex", "a" + (Time - 1)));//time - 1 because this is the action that generated the state, hence its index is i-1
                    pChoice.AddConstant(new Constant("ChoiceIndex", "c" + iRandomIdx));
                    State s = this;
                    while (s != null)
                    {
                        s.m_lPredicates.Add(pChoice);
                        s = s.m_sPredecessor;
                    }
                }
                else if (cf.Operator == "and")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        if (f is PredicateFormula)
                        {
                            AddEffect(((PredicateFormula)f).Predicate);
                        }
                        else
                            AddEffects(f);
                    }
                }
                else if (cf.Operator == "when")
                {
                    if (m_sPredecessor.Contains(cf.Operands[0]))
                        AddEffects(cf.Operands[1]);
                }
                else
                    throw new NotImplementedException();
            }
        }

        public void GetApplicableEffects(Formula fEffects, HashSet<Predicate> lAdd, HashSet<Predicate> lDelete)
        {
            if (fEffects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)fEffects).Predicate;
                if (p.Negation)
                    lDelete.Add(p);
                else
                    lAdd.Add(p);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof" || cf.Operator == "or")//BUGBUG - should treat or differently
                {
                    int iRandomIdx = RandomGenerator.Next(cf.Operands.Count);
                    GetApplicableEffects(cf.Operands[iRandomIdx], lAdd, lDelete);
                    GroundedPredicate pChoice = new GroundedPredicate("Choice");
                    pChoice.AddConstant(new Constant("ActionIndex", "a" + (Time - 1)));//time - 1 because this is the action that generated the state, hence its index is i-1
                    pChoice.AddConstant(new Constant("ChoiceIndex", "c" + iRandomIdx));
                    State s = this;
                    while (s != null)
                    {
                        s.m_lPredicates.Add(pChoice);
                        s = s.m_sPredecessor;
                    }
                }
                else if (cf.Operator == "and")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        GetApplicableEffects(f, lAdd, lDelete);
                    }
                }
                else if (cf.Operator == "when")
                {
                    if (Contains(cf.Operands[0]))
                        GetApplicableEffects(cf.Operands[1], lAdd, lDelete);
                }
                else if (cf is ParametrizedFormula)
                {
                    ParametrizedFormula pf = (ParametrizedFormula)cf;
                    foreach (Formula fNew in pf.Ground(Problem.Domain.Constants))
                        GetApplicableEffects(fNew, lAdd, lDelete);
                }
                else
                    throw new NotImplementedException();
            }
        }

        public Formula Observe(Formula fObserve)
        {
            if (fObserve is PredicateFormula)
            {
                Predicate pObserve = ((PredicateFormula)fObserve).Predicate;
                foreach (Predicate pCurrent in Predicates)
                {
                    if (pObserve.Equals( pCurrent ))
                    {
                        return new PredicateFormula(pCurrent);
                    }
                }
                return new PredicateFormula(pObserve.Negate());
            }
            throw new NotImplementedException("Not handling compound formulas for observations");
        }

        public void RemoveNegativePredicates()
        {
            HashSet<Predicate> lFiltered = new HashSet<Predicate>();
            foreach (Predicate pObserved in m_lPredicates)
            {
                if (pObserved.Negation == false)
                {
                    lFiltered.Add(pObserved);
                }
            }
            m_lPredicates = lFiltered;
            MaintainNegations = false;
        }
        public override string ToString()
        {
            foreach (Predicate p in Predicates)
                if (p.Name == "at" && !p.Negation)
                    return p.ToString();
            return "";
        }
        public override int GetHashCode()
        {
            if (code != -1) return code;
            foreach (GroundedPredicate gp in m_lPredicates)
                code += gp.GetHashCode();
            return code;
        }
        public KnowledgeState CreateKnowledgeState()
        {
            KnowledgeState kState = new KnowledgeState(Problem);
            foreach (Predicate p in Predicates)
                kState.m_lPredicates.Add(p);
            return kState;
        }

        public bool Contains(Predicate p)
        {
            if (p.Negation)
                return !Predicates.Contains(p.Negate());
            return Predicates.Contains(p);                   
        }
        public State ApplyFormulaEffectII(CompoundFormula eff, Dictionary<Predicate, HashSet<Predicate>> mutex, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, bool[] actionVector, List<Action> pablicActions, List<Predicate> preCon)
        {
            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;

            if (eff != null)
            {
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(eff, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet = new HashSet<Predicate>();

                foreach (GroundedPredicate p in lAddList)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet.Contains(mp))
                                mutexSet.Add(mp);
                        }
                    }
                }

                foreach (GroundedPredicate p in preCon)
                {

                    if (!mutex.ContainsKey(p))
                        continue;
                    foreach (Predicate mp in mutex[p])
                    {
                        if (!mutexSet.Contains(mp))
                            mutexSet.Add(mp);
                    }

                }

                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet.Contains(oldP))
                    {
                        dell.Add(oldP);


                    }

                }

                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    if (canGet.ContainsKey(pdell))
                    {
                        foreach (Action act in canGet[pdell])
                        {
                            actionVector[act.index] = false;
                        }
                    }
                }

                foreach (GroundedPredicate p in lDeleteList)
                {
                  //  if (PublicPredicates.Contains((GroundedPredicate)p.Negate()))
                 //   {
                        sNew.AddEffectII(p);
                        if (!PublicPredicates.Contains(p))
                        {
                           GroundedPredicate ngp = (GroundedPredicate)p.Negate();
                           if (canGet.ContainsKey(ngp))
                            {
                                foreach (Action act in canGet[ngp])
                                {
                                    actionVector[act.index] = false;
                                }
                            }
                        }
                   // }
                }

                foreach (GroundedPredicate p in lAddList)
                {
                    sNew.AddEffectII(p);
                }
            }

            return sNew;
        }
        public State PassiveApplyFormulaEffect(CompoundFormula eff, Dictionary<Predicate, HashSet<Predicate>> mutex, HashSet<GroundedPredicate> PublicPredicates, Dictionary<GroundedPredicate, List<Action>> canGet, bool[] actionVector, List<Action> privateActions, Dictionary<GroundedPredicate, int> publicPre)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;



            if (eff != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(eff, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet1 = new HashSet<Predicate>();

                foreach (GroundedPredicate p in lAddList)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet1.Contains(mp))
                                mutexSet1.Add(mp);
                        }
                    }
                }


                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet1.Contains(oldP))
                    {
                        dell.Add(oldP);
                    }


                }



                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    if (canGet.ContainsKey(pdell))
                    {
                        foreach (Action act in canGet[pdell])
                        {
                            actionVector[act.index] = false;
                            //   actionVector[privateActions.IndexOf(act)] = false;
                        }
                    }
                }


                foreach (GroundedPredicate p in lDeleteList)
                {
                    if (PublicPredicates.Contains((GroundedPredicate)p.Negate()))
                    {

                        sNew.AddEffectII(p);
                        if (publicPre.ContainsKey(p))
                           publicPre.Remove((GroundedPredicate)p.Negate());
                    }
                }
                foreach (GroundedPredicate p in lAddList)
                {
                    if (PublicPredicates.Contains(p))
                    {
                        sNew.AddEffectII(p);
                        if (!publicPre.ContainsKey(p))
                            publicPre.Add(p, 0);
                    }

                }

            }

            return sNew;
        }
        public State ApplyFormulaEffect(CompoundFormula eff, Dictionary<Predicate, HashSet<Predicate>> mutex)
        {

            State sNew = new State();
            sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            sNew.Problem = Problem;



            if (eff != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(eff, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();
                HashSet<Predicate> mutexSet = new HashSet<Predicate>();

                foreach (GroundedPredicate p in lAddList)
                {
                    
                        if (!mutex.ContainsKey(p))
                            continue;
                        foreach (Predicate mp in mutex[p])
                        {
                            if (!mutexSet.Contains(mp))
                                mutexSet.Add(mp);
                        }
                    
                }

              
                foreach (Predicate oldP in sNew.m_lPredicates)
                {


                    if (mutexSet.Contains(oldP))
                    {
                        dell.Add(oldP);


                    }

                }



                foreach (GroundedPredicate pdell in dell)
                {
                    sNew.m_lPredicates.Remove(pdell);
                    
                }

                foreach (GroundedPredicate p in lDeleteList)
                {
                   
                        sNew.AddEffectII(p);
                    
                }

                foreach (GroundedPredicate p in lAddList)
                {

                    sNew.AddEffectII(p);



                }


            }

            return sNew;
        }
        public void FullApplyFormulaEffect(CompoundFormula eff)
        {

            // State sNew = new State();
            // sNew.m_lPredicates = new HashSet<Predicate>(m_lPredicates);
            // sNew.Problem = Problem;



            if (eff != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(eff, lAddList, lDeleteList);
                List<Predicate> dell = new List<Predicate>();






                foreach (GroundedPredicate pdell in dell)
                {
                    this.m_lPredicates.Remove(pdell);

                }

                foreach (GroundedPredicate p in lDeleteList)
                {

                    this.AddEffectII(p);

                }

                foreach (GroundedPredicate p in lAddList)
                {

                    this.AddEffectII(p);

                }


            }


        }
        public bool FullApplyII(Action a)
        {
            if (a.Preconditions != null && !a.Preconditions.IsTrue(m_lPredicates, MaintainNegations))
                return false;


            if (a.Effects == null)
                return true;

            if (a.Effects != null)
            {

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (GroundedPredicate p in lDeleteList)
                {


                    this.AddEffectII(p);

                }
                foreach (GroundedPredicate p in lAddList)
                {

                    this.AddEffectII(p);


                }

            }
            return true;

        }
    }
}
