
//using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Planning;
using System;
using System.IO;

namespace Planning
{
    class HarderProblemsAlg
    {
        public Dictionary<string, List<Action>> agentActions = null;
        public Dictionary<string, HashSet<GroundedPredicate>> agentPredicate = null;
        bool chack=false;
        bool first = true;
        int numberOfAgent=-1;
        bool firstIteration = true;
        public List<Action> publicAction = null;
        public List<Action> privateAction = null;
        Dictionary<string, List<Action>> agentActionl;
        Dictionary<Action, List<Block>> preObservesion = null;
        Dictionary<Action, List<Action>> makeChangeActions = null;
        List<Action> allActions = new List<Action>();
        List<Action> preOb = new List<Action>();
        List<Action> obs = new List<Action>();
        int breakv=0;
        //private int count = 1;
       // List<List<key_value>> newTypeLandmarks;
        Dictionary<GroundedPredicate, int> disTable; 
        private bool isFirst = true;
        List<Planning.Action> concludesAction;
        Dictionary<int,string> preAction;
        string[] options = { "true", "false" };
        public enum replyType{True,False,first};
        List<Action> groundedAction = null;
        public List<Landmark> discoverdLandmark = null;
        public List<Order> orderList = null;
        public List<Order> ReasonableOrderList = null;
        Queue<Landmark> queue = null;
        Dictionary<GroundedPredicate, List<Action>> observeDomain = null;
        Problem problam = null;
        Domain domain = null;
        public Dictionary<Landmark, List<Action>> LandmarkWithHerAchieve = null;
        //  List<Landmark> allLandmark = null;
        public Dictionary<Predicate, List<Action>> allFactsWithActAchieve = null;
        Dictionary<Predicate, List<Predicate>> allFactsWitTheirEffect = null;
        List<Order> TempOrder = null;
        Dictionary<GroundedPredicate, List<Action>> hideGroundedPredicate;
        List<GroundedPredicate> ObserveGroundedPredicateList;
        List<Action> ObserveAction;
        List<string> missingDomain = new List<string>();
        HashSet<Action> notRelevantActions;
        List<GroundedPredicate> oldState = new List<GroundedPredicate>();
        ListOfStates  newStates;
        ComplexState comState;
        HashSet<Action> runOnes;
        Action lastRecommendedActin=null;
        public Action pppp = null;
        bool isGoal;
        public HashSet<MutuallyExclusiveFacts> me = null;
        //public StreamWriter tmpSW = new StreamWriter("ActioGrade.txt", false);
        public HarderProblemsAlg(Problem prob, Domain d)
        {
            runOnes = new HashSet<Action>();
            preAction = new Dictionary<int, string>();
            Debug.WriteLine("start : intial HarderProblemsAlg");

            

            domain = d;
            problam = prob;

            notRelevantActions = new HashSet<Action>();
            newStates = new ListOfStates();
         

            
            
            
           
            discoverdLandmark = new List<Landmark>();
            
            
            groundedAction = domain.GroundAllActions();
            

            queue = new Queue<Landmark>();
            LandmarkWithHerAchieve = new Dictionary<Landmark, List<Action>>();
            allFactsWithActAchieve = new Dictionary<Predicate, List<Action>>();
            //allFactsWitTheirEffect = new Dictionary<GroundedPredicate, List<Action>>();


            FillFact(allFactsWithActAchieve);
            

           // CleanActionList_2();
           // DivideToAgents(groundedAction);
            

            FillFactDictionary(allFactsWithActAchieve, null);
           // FillFactDictionaryII(out allFactsWithActAchieve, out allFactsWitTheirEffect);
           // FindPublicAndPrivateAction(out publicAction, out privateAction);

            Debug.WriteLine("Start : FindLandmark");
            FindLandmarksNow();
            
            //discoverdLandmark = null;
            Debug.WriteLine("done finding Landmarks");
            Debug.WriteLine("done intial HarderProblemsAlg");
            Debug.WriteLine("Play:");

            List<Landmark> landmarks = new List<Landmark>();
            foreach (Landmark l in discoverdLandmark)
            {
                if (!l.facts.ElementAt(0).Value.Equals("start"))
                    landmarks.Add(l);
            }

            discoverdLandmark = landmarks;
           // me = FindDTG();

          

        }
       
        private void DivideToAgents(List<Action> actions)
    {
        agentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
        List<Action> dell = new List<Action>();
        int fail = 0;
        foreach (Action act in actions)
        {
            if (((GroundedPredicate)act.HashEffects.ElementAt(0)).Name.Equals("P_FALSE"))
            {
                dell.Add(act);
                continue;
            }
            foreach (GroundedPredicate p in act.HashPrecondition)
            {
                if (act.agent != null) break;
                foreach (var arg in p.Constants)
                {
                    if ((arg.Name.Contains("rover") && arg.Name.Length == 6) || arg.Name.Contains("plane") || arg.Name.Contains("apn") || arg.Name.Contains("satellite") || arg.Name.Contains("aircraft") || arg.Name.Contains("tru"))
                    {
                        act.agent = arg.Name;
                        if (!agentPredicate.ContainsKey(arg.Name))
                        {
                            agentPredicate.Add(arg.Name, new HashSet<GroundedPredicate>());
                        }
                        break;
                    }
                }

            }
            if (act.agent == null)
            {
                fail++;
            }
            else
            {
                foreach (GroundedPredicate gp in act.HashPrecondition)
                {
                    if (!agentPredicate[act.agent].Contains(gp))
                    {
                        agentPredicate[act.agent].Add(gp);
                    }
                }
            }
        }

            foreach(Action dellAct in dell)
            {
                actions.Remove(dellAct);
            }

    }
            
        
        private Dictionary<GroundedPredicate,int> FindDisTable(HashSet<GroundedPredicate> s)
        {
            Dictionary<GroundedPredicate, int> ans = new Dictionary<GroundedPredicate, int>();
            List<Action> actions =new List<Action>();
            foreach(Action act in privateAction)
            {
                
                {
                    actions.Add(act);
                }
            }
            foreach (GroundedPredicate gp in s)
            {
                ans.Add(gp, 0);
            }
            bool flag = true;
            int level=0;
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
                                if (!s.Contains(gp)&&!tmp.Contains(gp))
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
                    ans.Add(gp,level);
                }
                foreach (Action dellact in dell)
                {
                    actions.Remove(dellact);
                }
            }
            return ans;

        }

        private int FindDis(Action act)
        {
            if (act.Preconditions==null)
                return 0;
            int sum=0;
            foreach (GroundedPredicate gp in act.HashPrecondition)
            {
                if (!disTable.ContainsKey(gp))
                    return int.MaxValue;

                sum += disTable[gp];
            }
            return sum;
        }
        private void FillFact(Dictionary<Predicate, List<Action>> facts)
        {
            
            
            foreach (GroundedPredicate prop in problam.Known)
            {
                /* GroundedPredicate prop2 = new GroundedPredicate(prop);
                 if (prop.Negation)
                 {
                     prop2.Negation = false;
                 }
                 else
                 {
                     prop2.Negation = true;
                 }*/
                List<Action> templist = new List<Action>();
                facts.Add(prop, templist);
                //List<Action> templist2 = new List<Action>();
                //AddFact(prop2, templist);
            }
            foreach (Action act in groundedAction)
            {
                if (act.Effects != null)
                {
                    foreach (GroundedPredicate prop1 in act.HashEffects)
                    {
                        if (!facts.ContainsKey(prop1))
                        {
                            List<Action> templist = new List<Action>();

                            facts.Add(prop1, templist);

                        }




                    }
                }
                
                }
            
            // not nessery
                   

        }
        private void FillFactDictionary(Dictionary<Predicate, List<Action>> facts, Dictionary<GroundedPredicate, List<Action>> facts2)
        {
            List<Action> del = new List<Action>();
            List<Action> add = new List<Action>();
            List<Action> listOfActions;
            foreach (Action a in groundedAction)
            {
                if (a.Effects != null)
                 {                                      
                        allActions.Add(a);
                 }
  
            }
          
            //groundedAction.AddRange(add);
           /* foreach (GroundedPredicate prop in problam.Known)
            {
                /* GroundedPredicate prop2 = new GroundedPredicate(prop);
                 if (prop.Negation)
                 {
                     prop2.Negation = false;
                 }
                 else
                 {
                     prop2.Negation = true;
                 }*/
                //List<Action> templist = new List<Action>();
               // AddFact(prop, templist);
                //List<Action> templist2 = new List<Action>();
                //AddFact(prop2, templist);
          //  }
            foreach (Action act in groundedAction)
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
                
                if (facts2 != null)
                {
                    if (act.Preconditions != null)
                    {
                        foreach (GroundedPredicate prop2 in act.HashEffects)
                        {

                            if (!facts2.ContainsKey(prop2))
                            {
                                List<Action> templist = new List<Action>();
                                templist.Add(act);

                                facts2.Add(prop2, templist);


                            }
                            else
                            {

                                facts2[prop2].Add(act);
                            }
                        }




                    }

                }
            }
            if (false)//facts2 != null)
            {
                Dictionary<GroundedPredicate, List<GroundedPredicate>> tmp = new Dictionary<GroundedPredicate, List<GroundedPredicate>>();
                foreach (KeyValuePair<GroundedPredicate, List<Action>> po in facts2)
                {
                    if (!facts.ContainsKey(po.Key))
                    {
                        tmp.Add(po.Key, null);

                    }

                }

                foreach (KeyValuePair<GroundedPredicate, List<GroundedPredicate>> po in tmp)
                {
                    facts2.Remove(po.Key);
                }
            }

        }

        private void FindconcludesAction2()
        {
            
        }


        private void CleanActionList_2()
        {
            HashSet<GroundedPredicate> set = new HashSet<GroundedPredicate>();
            HashSet<Action> pAction = new HashSet<Action>();
            bool flag = true;

            foreach (GroundedPredicate gp in problam.Known)
            {
                set.Add(gp);
            }


            while (flag)
            {
                flag = false;
               
                foreach (Action act in groundedAction)
                {
                    if (!pAction.Contains(act))
                    {
                        if (Contains(set, act.HashPrecondition))
                        {
                            foreach (GroundedPredicate gp in act.HashEffects)
                            {
                                if (!set.Contains(gp))
                                {
                                    flag = true;
                                    set.Add(gp);
                                }
                            }

                            pAction.Add(act);
                        }
                    }
                }
                
            }
            groundedAction = pAction.ToList();
        }
        private void CleanActionList()
        {
            HashSet<Action> notPosibleAction = new HashSet<Action>();
            HashSet<GroundedPredicate> notPosiblePrdicate = new HashSet<GroundedPredicate>();
            /*  foreach (KeyValuePair<GroundedPredicate,List<Action>> gp in allFactsWithActAchieve)
              {
                  if (gp.Value.Count == 0 && !problam.Known.Contains(gp.Key))
                  {
                      notPosiblePrdicate.Add(gp.Key);
                  }
              }*/
            foreach (Action act in groundedAction)
            {
                bool flag = true;
                foreach (GroundedPredicate pre in act.HashPrecondition)
                {
                    if (!allFactsWithActAchieve.Keys.Contains(pre))
                    {
                        flag = false;
                    }
                }
                if (!flag)
                {
                    notPosibleAction.Add(act);

                }
            }
            List<Action> tmp = new List<Action>();
           /* for (int i = 0; i < groundedAction.Count; i++)
            {

                if (notPosibleAction.Contains(groundedAction[i]))
                { 
                    groundedAction.RemoveAt(i);
                    i--;
                }

            }*/
           foreach(Action act in groundedAction)
            {

                if (!notPosibleAction.Contains(act))
                {
                    tmp.Add(act);
                }

            }
           groundedAction = new List<Action>(tmp);
            /*
            List<Action> delList= new List<Action>();
            foreach (Action act in groundedAction)
            {
                if (act.Effects != null) continue;

                bool dell = true;
                if (act.Observe != null)
                {
                    foreach (GroundedPredicate gP in act.HashObserve)
                    {
                        GroundedPredicate a1 = new GroundedPredicate(gP);
                            GroundedPredicate a2 = new GroundedPredicate(gP);
                            a2.Negation = !(a2.Negation);
                            if (!(problam.Known.Contains(a1) || problam.Known.Contains(a2)))
                            {
                                dell = false;
                                break;
                            }
                    }
                    if (dell)
                    {
                        delList.Add(act);

                    }

                }
            }

            foreach (Action delAct in delList)
            {
                groundedAction.Remove(delAct);
            }
            */
          


        }

        //Find landmarks
        public void FindLandmarksNow()
        {
            Landmark landmark;
            int maxVlaue = 250;

            discoverdLandmark = new List<Landmark>();
            orderList = new List<Order>();
            TempOrder = new List<Order>();

           /* foreach (GroundedPredicate prop in problam.Known)
            {
                Landmark tempLandmark = new Landmark("fact");
                tempLandmark.AddFact(prop, "start");
                bool flg = InserLandmark(tempLandmark, null, null);
            }*/

            foreach (GroundedPredicate prop in problam.Goal.GetAllPredicates())
            {
               // if (!problam.Known.Contains(prop))
                {
                    Landmark tempLandmark = new Landmark("fact", true);
                    tempLandmark.AddFact(prop, "Goal");
                    tempLandmark.worth = 2;
                    bool flg = InserLandmark(tempLandmark, null, null);
                    if (flg)
                    {
                        queue.Enqueue(tempLandmark);
                    }
                    else
                        discoverdLandmark.Add(tempLandmark);
                }

            }

            while (queue.Count != 0)
            {

                landmark = queue.Dequeue();
                /* List<Action> pb = new List<Action>();// FindPossiblyBefore(landmark);
                 foreach (GroundedPredicate gp in landmark.facts.Keys)
                 {
                     pb.AddRange( allFactsWithActAchieve[gp] );
                 }*/
                List<Action> pb = FindPossiblyBefore(landmark);
                bool flag2 = false;
                if (pb.Count > 0)
                {
                    HashSet<GroundedPredicate> oldFacts = new HashSet<GroundedPredicate>();
                    Action firstAction = pb[0];
                    foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                    {
                        bool flag = true;
                        foreach (Action act in pb)
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
                            Landmark newLandmark = new Landmark("fact", false);
                            newLandmark.AddFact(prop, "first_round");
                            newLandmark.worth = 1;// landmark.worth - 10;
                            oldFacts.Add(prop);
                            bool flg = InserLandmark(newLandmark, landmark, "greedy-necessary");
                            if (flg)
                            {
                                queue.Enqueue(newLandmark);
                            }
                            // }
                        }
                    }
                    if (!flag2 && pb.Count > 1) //&& landmark.facts.Count < 2)
                    {
                        flag2 = true;
                        firstAction = pb[0];
                        pb.RemoveAt(0);
                        foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                        {
                            if (!problam.Known.Contains(prop) && !oldFacts.Contains(prop))
                            {
                                int counter = 0; ;
                                Landmark newLandmark = new Landmark("Disjunctive", false);
                                newLandmark.worth = 1;// landmark.worth - 10;
                                newLandmark.AddFact(prop, "first_round");
                                foreach (Action act in pb)
                                {
                                    bool f = false;
                                    foreach (GroundedPredicate prop2 in act.HashPrecondition)
                                    {
                                        if (prop2.Name == prop.Name && !problam.Known.Contains(prop2) && !oldFacts.Contains(prop2))
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
                                             if (!problam.Known.Contains(prop2) && !oldFacts.Contains(prop2))
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
                                if (counter == pb.Count && newLandmark.facts.Count > 1)
                                {
                                    bool flg = InserLandmark(newLandmark, landmark, "greedy-necessary");
                                    if (flg)
                                    {
                                        queue.Enqueue(newLandmark);
                                    }
                                }
                            }
                        }
                    }

                }



            }
            /*
            foreach (Landmark tmpLandmark in discoverdLandmark)
            {
                if (tmpLandmark.facts.Values.ElementAt(0) != "start")
                    //FindAllNecessaryOrder(tmpLandmark);

                foreach (Order order in orderList)
                {
                    if (order.lendmark2 == tmpLandmark)
                    {
                        if (!orderList.Contains(order))
                        {
                            orderList.Add(order);

                        }
                        break;
                    }

                }
            }
             */
            List<Landmark> dellList = new List<Landmark>();
            foreach (Landmark land in discoverdLandmark)
            {
                if (land.facts.Values.ElementAt(0) == "start")
                {
                    bool Flag = true;
                    foreach (Order order in orderList)
                    {
                        if (order.lendmark1 == land)
                        {
                            Flag = false;
                            break;
                        }
                    }
                    if (Flag)
                        dellList.Add(land);
                }


            }
            foreach (Landmark dellLand in dellList)
            {
                discoverdLandmark.Remove(dellLand);
            }

        }







        //insert landmark
        private bool InserLandmark(Landmark land, Landmark land2, string orderType)
        {
            if (discoverdLandmark == null) return false;

            if (land.type == "fact")
            {
                Landmark delLandmark = null;
                bool flag = true;
                foreach (KeyValuePair<GroundedPredicate, string> fact in land.facts)
                {
                    if (problam.Known.Contains(fact.Key))
                        return false;
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
                    if (problam.Known.Contains(fact.Key))
                        return false;
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




        //find possible before

        private List<Action> FindPossiblyBefore(Landmark landmark)
        {
            HashSet<Action> actions = new HashSet<Action>();
            List<Action> opsionalActions = new List<Action>();

            foreach (Action act in groundedAction)
            {
                bool flag = true;
                foreach (KeyValuePair<GroundedPredicate, string> prop in landmark.facts)
                {
                    if (act.Effects != null)
                    {
                        if (act.HashEffects.Contains(prop.Key))
                        {
                            opsionalActions.Add(act);
                            flag = false;
                            break;
                        }
                    }
                    
                }
                if (flag)
                {
                    actions.Add(act);
                }
            }
            

            bool flag2 = true;

            //State copyState = new State(problam);
            HashSet<GroundedPredicate> StateGroundedPredicates = new HashSet<GroundedPredicate>();

            foreach (GroundedPredicate prop in problam.Known)
            {
                //GroundedPredicate newProp = new GroundedPredicate(prop);

                //foreach (string str in prop.Objects)
                //{
                  //  newProp.Objects.Add(str);

//                }

                //copyState.AddGroundedPredicateWithoutcheck(newProp);
                StateGroundedPredicates.Add(prop);
            }
            
            //List<Action> possibaleActionList= new List<Action>();
            List<Action> allActions=new List<Action>();

           

            while (flag2)
            {
                flag2 = false;
                List<Action> tempActionList = new List<Action>();
               // List<GroundedPredicate> tempList = new List<GroundedPredicate>();
                foreach (Action act in actions)
                {
                    if (Contains(StateGroundedPredicates, act.HashPrecondition))
                    {
                        tempActionList.Add(act);
                        // possibaleActionList.Add(act);   
                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!StateGroundedPredicates.Contains(addProp))
                                {                    
                                    //copyState.AddGroundedPredicateWithoutcheck(addProp);
                                    StateGroundedPredicates.Add(addProp);
                                    //tempList.Add(addProp);
                                    flag2 = true;
                                }

                            }
                        }
                        
                    }


                }

                foreach (Action action in tempActionList)
                {
                    actions.Remove(action);

                }



            }

            List<Action> PossibaleAcive = new List<Action>();
            foreach (Action act in opsionalActions)
            {

                if (Contains(StateGroundedPredicates, act.HashPrecondition))
                {
                    PossibaleAcive.Add(act);
                }
            }
            /* find natural order
            Landmark opsionalLandmark2 = new Landmark("Disjunctive");
            foreach (KeyValuePair<GroundedPredicate, List<Action>> prop in allFactsWithActAchieve)
            {
                Landmark opsionalLandmark1 = new Landmark("fact");

                if (!StateGroundedPredicates.Contains(prop.Key))
                {
                    opsionalLandmark2.AddFact(prop.Key, "first_round");
                    opsionalLandmark1.AddFact(prop.Key, "first_round");
                    Order order = new Order("natural", landmark, opsionalLandmark1);
                    TempOrder.Add(order);
                }

            }
            if (opsionalLandmark2.facts.Count() > 0)
            {

                Order order = new Order("natural", landmark, opsionalLandmark2);
                TempOrder.Add(order);
            }

            */



            return PossibaleAcive;


        }

        private Action FindBestObserveAct(HashSet<GroundedPredicate> s, ListOfStates ans, HashSet<Action> notRelevantActions, List<Predicate> knowledge, HashSet<GroundedPredicate> state)
        {

           
            //List<Action> actionsLandmarks = new List<Action>();
            Dictionary<Action, int> dis = new Dictionary< Action,int>();
            Dictionary<Action, List<int>> dic = new Dictionary<Action, List<int>>();
            List<ListOfStates> ansState = new List<ListOfStates>();

            disTable = FindDisTable(state);
            //List<Action> notRelevantForAllState = new List<Action>();
            if(notRelevantActions.Count==0)
            {

               
                List<Action> firstRoundActions = new List<Action>();
                firstRoundActions.AddRange(privateAction);
                 
                HashSet<GroundedPredicate> tmpStateGroundedPredicates = new HashSet<GroundedPredicate>();
                
                foreach (GroundedPredicate prop in s)
                {
                    GroundedPredicate newProp = new GroundedPredicate(prop);    
                    tmpStateGroundedPredicates.Add(newProp);
                }
                var g = problam.Goal;
                bool stop = false;
                while (!stop && !Contains(s,problam.Goal.GetAllPredicates()))
                {
                    List<Action> tempActionList = new List<Action>();
                    stop =true;
                    List<GroundedPredicate> tempList = new List<GroundedPredicate>();
                    foreach (Action act in firstRoundActions)
                    {
                        
                        if (Contains(s,act.HashPrecondition))
                        {
                            tempActionList.Add(act);
                            if (act.Effects != null)
                            {
                                foreach (GroundedPredicate addProp in act.HashEffects)
                                {
                                    if (!tmpStateGroundedPredicates.Contains(addProp))
                                    {

                                        //not good
                                       
                                            s.Add(addProp);

                                        tmpStateGroundedPredicates.Add(addProp);
                                        tempList.Add(addProp);
                                        stop = false;
                                    }

                                }
                            }
                            
                        }


                    }

                    foreach (Action action in tempActionList)
                    {
                        firstRoundActions.Remove(action);
                        notRelevantActions.Add((action));
                    }



                }
                if ((Contains(s,problam.Goal.GetAllPredicates())))
                {
                    return null;
                }


            }
            List<Action> relevantAction = new List<Action>();
            foreach (Action act in privateAction)
            {
                if (!notRelevantActions.Contains(act))
                {

                    relevantAction.Add(act);
                }
            }
            int numOfGroundedPredicate = s.Count();
            int numOfGroundedPredicateBeforeObserve = numOfGroundedPredicate;
            List<Landmark> notSatisfyLandmarks =new List<Landmark>(); 

            foreach (Landmark landmark in discoverdLandmark) 
            {
                
                bool flag=false;
                foreach (GroundedPredicate fact in landmark.facts.Keys)
                {
                    if (s.Contains(fact))
                    {
                        flag = true;
                        break;

                    }
                    

                }
                if(!flag)
                {
                    notSatisfyLandmarks.Add(landmark);
                }
            }

           // if (breakv == 11)
           // {
            //    breakv = breakv;
           // }

           // numOfGroundedPredicateBeforeObserve = s.m_lGroundedPredicates.Count();
            List<Action> publicActionsList = new List<Action>();
            List<Action> nPoPublicActionsList = new List<Action>();
            foreach (Action act in publicAction)
            {
                if (FindDis(act) != int.MaxValue)
                {
                    publicActionsList.Add(act);
                }
                else
                {
                    nPoPublicActionsList.Add(act);
                }
            }
            //foreach(Action dell in runOnes
            
           
             int count = 0;
             if (publicActionsList.Count == 0 )
                 return null;
             foreach (Action publicAct in publicActionsList)
            {
                count++;
                Action actionKey = publicAct;
                HashSet<GroundedPredicate> tmp = new HashSet<GroundedPredicate>();
                bool tmp2; 
                List<GroundedPredicate> tmp3 = new List<GroundedPredicate>();
                List<Action> nR = new List<Action>();
                Action obAct=null;
                //Action actionKey=null;
                List<int> valueAction = new List<int>();
                
                    bool keyF=false;
                    KeyValuePair<Action, Action> term = new KeyValuePair<Action, Action>();
                     

                    List<GroundedPredicate> addingknowledge = new List<GroundedPredicate>();
                    foreach (GroundedPredicate addgp in knowledge)
                    {
                        addingknowledge.Add(addgp);
                    }

                   obAct=publicAct;

                    if (obAct == null) //note:deal with missing information
                    {
                        int t = 9;
                    }



                    List<Action> notRelevant = new List<Action>();
                    HashSet<Action> actions = new HashSet<Action>();
                    actions.Add(obAct);
                    foreach (Action act in relevantAction)
                    {
                       
                           
                            actions.Add(act);
                        
                    }
                    
                    bool flag2 = true;

                    //State copyState = new State(problam);
                    HashSet<GroundedPredicate> StateGroundedPredicates = new HashSet<GroundedPredicate>();

                    foreach (GroundedPredicate prop in s)
                    {
                       // GroundedPredicate newProp = new GroundedPredicate(prop);
                        //copyState.AddGroundedPredicateWithoutcheck(prop);
                        StateGroundedPredicates.Add(prop);
                    }



                    while (flag2 && !Contains(StateGroundedPredicates, problam.Goal.GetAllPredicates()))
                        {

                            List<Action> tempActionList = new List<Action>();
                            flag2 = false;
                            List<GroundedPredicate> tempList = new List<GroundedPredicate>();
                            foreach (Action act in actions)
                            {
                                if (Contains(StateGroundedPredicates,act.HashPrecondition))
                                {
                                    tempActionList.Add(act);
                                    if (act.Effects != null)// && act.Observe == null)
                                    {
                                        foreach (GroundedPredicate addProp in act.HashEffects)
                                        {
                                            if (!StateGroundedPredicates.Contains(addProp))
                                            {
                                                bool mE=false;
                                                foreach(GroundedPredicate gpIter in knowledge)
                                                {
                                                    if (IsMutuallyExclusive(addProp, gpIter))
                                                    {
                                                        mE = true;
                                                        break;
                                                    }
                                                }
                                                if (!mE)
                                                {
                                                    //copyState.AddGroundedPredicateWithoutcheck(addProp);
                                                    StateGroundedPredicates.Add(addProp);
                                                    tempList.Add(addProp);
                                                    if (missingDomain.Contains(addProp.ToString()))
                                                    {
                                                        addingknowledge.Add(addProp);
                                                    }
                                                    flag2 = true;
                                                }
                                            }

                                        }
                                    }
                                   
                                }


                            }

                     


                        }
                  
                    nR.AddRange(notRelevant);

                    List<GroundedPredicate> addingGroundedPredicate = new List<GroundedPredicate>();
                    int sum=0;
                    foreach (GroundedPredicate gp in addingknowledge)
                    {
                        if(!knowledge.Contains(gp))
                        {
                            foreach (Action iterAct in nPoPublicActionsList)
                            {
                                if (iterAct.HashPrecondition.Contains(gp))
                                {
                                    sum++;
                                }
                            }

                        }
                    }
                    if (!Contains(StateGroundedPredicates,problam.Goal.GetAllPredicates()))
                    {
                        bool f = false;
                        tmp2 = f;
                        tmp3=addingknowledge;
                        
                        //if (true)//i==0)
                        {
                            List<int> tmpp = new List<int>();
                            if (StateGroundedPredicates.Count == numOfGroundedPredicate)
                            {
                                tmpp.Add(int.MinValue / 2);
                            }
                            else
                            {
                                int numOfSatisfiedLandmarks = SatisfyLandmark(StateGroundedPredicates, notSatisfyLandmarks);
                                
                                  tmpp.Add((StateGroundedPredicates.Count - numOfGroundedPredicateBeforeObserve)+numOfSatisfiedLandmarks+sum);
                                //tmpp.Add((StateGroundedPredicates.Count - numOfGroundedPredicateBeforeObserve) );
                                //tmpp.Add((sum));
                                //tmpp.Add(int.MinValue / 2);
                                //tmpp.Add((numOfSatisfiedLandmarks));
                                //tmpp.Add((StateGroundedPredicates.Count - numOfGroundedPredicateBeforeObserve)+numOfSatisfiedLandmarks);
                            }
                           // dic.Add(obAct, tmpp);

                            //actionKey = obAct;
                            valueAction = tmpp;

                        }
                       
                        //actionsLandmarks.Add(obAct);
                    }
                    else
                    {
                        bool f = true;
                        tmp2=true;
                        tmp3=addingknowledge;
                        //if (i==0)
                       // {
                            List<int> tmpp = new List<int>();
                            tmpp.Add((int.MaxValue-1)/2);
                            //actionKey = obAct;
                          
                            valueAction = tmpp;
                            //dic.Add(obAct, tmpp);

                       // }
                       
                    }

                    foreach (var v in StateGroundedPredicates)
                    {
                        tmp.Add(v);
                    }


             
                dic.Add(actionKey, valueAction);
                ListOfStates los = new ListOfStates();
                dis.Add(actionKey,FindDis(actionKey));
                los.notRelevantActions = nR;
                los.states = tmp;
                los.isGoal = tmp2;
                los.addingKnowledge = tmp3;
                ansState.Add(los);
            }

             Action bestAct = dic.ElementAt(0).Key;

             int max = -1;// dic.ElementAt(0).Value[0];
            //int high = 0;
           // int low=0;
            int counter = 0;
            int index = 0;
            List<int> maxList=new List<int>();
            maxList.Add(index);
            foreach (KeyValuePair<Action, List<int>> iter in dic)
            {
                if (max < iter.Value[0])
                {

                    bestAct = iter.Key;

                    max = (iter.Value[0]);
                    index = counter;
                    maxList = new List<int>();
                    maxList.Add(counter);
                }
                else
                {
                    if (max == iter.Value[0] && dis.ElementAt(counter).Value < dis.ElementAt(index).Value)
                    {

                        bestAct = iter.Key;
                        max = iter.Value[0];
                        index = counter;
                        maxList = new List<int>();
                        maxList.Add(counter);
                    }

                    else
                    {
                        if (max == iter.Value[0] && dis.ElementAt(counter).Value == dis.ElementAt(index).Value)
                        maxList.Add(counter);
                    }
                    if (max == iter.Value[0])
                    {
                        if(!maxList.Contains(counter))
                            maxList.Add(counter);
                    }
                }
                counter++;
            }
             Random rand = new Random();
             if (maxList.Count > 1)
             {
                 int randIndex = rand.Next(0, maxList.Count);
                 //index = maxList[randIndex];
             }
            ans.states = ansState.ElementAt(index).states;
            
            
                ans.isGoal = ansState.ElementAt(index).isGoal;



                ans.notRelevantActions = ansState.ElementAt(index).notRelevantActions;


                ans.addingKnowledge = ansState.ElementAt(index).addingKnowledge;
            
            //ans = ansState.ElementAt(index);
          //  runOnes.Add(bestAct);          
           // runOnes.Add(PairsOfObserveAction[bestAct]);
            
           // ObserveAction.Remove(bestAct);
            //ObserveAction.Remove(PairsOfObserveAction[bestAct]);
                //tmpSW.WriteLine(bestAct.Name + "   " + dic[bestAct][0]);
               // tmpSW.Flush();
            return bestAct;
            
        }


       

       

        public void GetFirstObserveAction(out Action actName, out List<Predicate> fGoal, out bool isFinal, State pssCurrent)
        {
            //pssCurrent = new PartiallySpecifiedState(pssCurrent);
           // preActionName = null;
            


            HashSet<GroundedPredicate> state = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in pssCurrent.m_lPredicates)
            {
                state.Add(gp);
            }
            
            
            //Debug.WriteLine("start : GetFirstObserveAction");
            
            //Queue<ComplexState> stateList = new Queue<ComplexState>();
            if (isGoal==true)
            {
                actName = null;
                
                isFinal = true;
               
                //states = null;

                fGoal = problam.Goal.GetAllPredicates().ToList();
                return;
            }


            if (firstIteration)
            {
                comState = new ComplexState(pssCurrent);
                firstIteration = false;
            }
            else
            {
                
                comState = new ComplexState(newStates.states, comState.stringList, comState.actionList, newStates.addingKnowledge);
                //comState.actionList.Add(lastRecommendedActin);
                //comState.stringList.Add(options[0]);
                //stateList.Enqueue(newComplexState);
                foreach (Action tempact in newStates.notRelevantActions)
                {
                    notRelevantActions.Add(tempact);
                }
            }
           


            newStates = new ListOfStates();
             
           
             
                // State st1 = newp.GetInitialBelief().ChooseState(false);
                 //State st2 = new State(st1);


                 breakv++;
                 
                     //Debug.WriteLine(System.DateTime.Now.Hour + " " + System.DateTime.Now.Minute + " " + System.DateTime.Now.Second + " " + System.DateTime.Now.Millisecond);
                     
                  
                        // if (counter>5) throw (new Exception() );
                      // lastRecommendedActin = FindBestObserveAct(comState.state,newStates,notRelevantActions,notRelevantActions)
                     lastRecommendedActin = FindBestObserveAct(comState.state, newStates, notRelevantActions, comState.knowledge, state);
           
                          
                     if (lastRecommendedActin == null)
                     {
                         actName = null;
                         
                         isFinal = true;
                         
                         
                        // states = null;
                          
                         fGoal = problam.Goal.GetAllPredicates().ToList();
                         return;
                     }
                     //Debug.WriteLine(System.DateTime.Now.Hour + " " + System.DateTime.Now.Minute + " " + System.DateTime.Now.Second + " " + System.DateTime.Now.Millisecond);
                     //Debug.WriteLine("done: GetFirstObserveAction");
                     
                // List<Action> t = new List<Action>();
                 
                
               /*  Debug.WriteLine("do:");
                
                     foreach (GroundedPredicate preAct in lastRecommendedActin.Preconditions)
                     {
                         int i = 1;
                         Debug.WriteLine(i + ") " + preAct.ToString());
                         i++;
                     }
                 
                 Debug.WriteLine("__");
                 Debug.WriteLine(lastRecommendedActin.Name);*/
                 //actName = new List<string>();
               

                  actName=lastRecommendedActin;
                 // Action act = preAction[lastRecommendedActin.ToString];
                  
                  isFinal = newStates.isGoal;
                  
                 
                 // states = newStates.states;
                 
                  fGoal = lastRecommendedActin.HashPrecondition;
                  isGoal = newStates.isGoal;
                 



                  
           
           // if (lastRecommendedActin.Name == "sense-door:p1-9:p2-9")
           // {

            //    int ttt = 9;
           // }
        }



      

        private int SatisfyLandmark( HashSet<GroundedPredicate> newState,List<Landmark> landmarks )
        {
            int ans = 0;
            foreach (Landmark landmark in landmarks)
            {
                foreach(GroundedPredicate fact in landmark.facts.Keys)
                {
                    if(newState.Contains(fact))
                    {
                        ans += landmark.worth;
                        break;
                        
                    }


                }
            }
            return ans;
        }
        
        
        
       /* private void FindLandmarksZhuAndGivan()
        {
            Dictionary<GroundedPredicate, List<GroundedPredicate>> allGroundedPredicateWithIsLandmarks = new Dictionary<GroundedPredicate, List<GroundedPredicate>>();
            //HashSet<GroundedPredicate> StateGroundedPredicates = new HashSet<GroundedPredicate>();
            State copyState =new State(problam);
            foreach (GroundedPredicate gp in problam.Known)
            {
                    List<GroundedPredicate> tmplist= new List<GroundedPredicate>();
                    tmplist.Add(gp);
                    allGroundedPredicateWithIsLandmarks.Add(gp,tmplist);
                    copyState.AddGroundedPredicateWithoutcheck(gp);            
            }
            HashSet<Action> actions =new HashSet<Action>();
            
            foreach (Action act  in groundedAction)
            {
                actions.Add(act);
            }

            bool stop = false;
            while(!stop)
            {
                stop = true;
                List<Action> tempActionList = new List<Action>();
                // List<GroundedPredicate> tempList = new List<GroundedPredicate>();
                foreach (Action act in actions)
                {
                    if (copyState.ContainsGroundedPredicates(act.HashPrecondition))
                    {
                        tempActionList.Add(act);
                        // possibaleActionList.Add(act);
                        stop = false;
                        if (act.Effects != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashEffects)
                            {
                                if (!copyState.ContainsGroundedPredicate(addProp))
                                {
                                
                                    List<GroundedPredicate> temp =new List<GroundedPredicate>();
                                    temp.Add(addProp);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        temp.Add(groundedGroundedPredicate);
                                    }
                                   
                                    allGroundedPredicateWithIsLandmarks.Add(addProp, temp);
                                    copyState.AddGroundedPredicateWithoutcheck(addProp);
                                    //StateGroundedPredicates.Add(addProp);
                                    //tempList.Add(addProp);
                                    //flag2 = true;
                                }
                                else
                                {
                                    List<GroundedPredicate> allPreFact = new List<GroundedPredicate>();
                                    List<GroundedPredicate> temp = new List<GroundedPredicate>();
                                    temp.Add(addProp);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        allPreFact.AddRange(allGroundedPredicateWithIsLandmarks[groundedGroundedPredicate]);
                                    }
                                    if (!allPreFact.Contains(addProp))
                                    {
                                        foreach (GroundedPredicate groundedGroundedPredicate in allGroundedPredicateWithIsLandmarks[addProp])
                                        {
                                            if (allPreFact.Contains(groundedGroundedPredicate))
                                            {
                                                temp.Add(groundedGroundedPredicate);
                                            }
                                        }
                                        allGroundedPredicateWithIsLandmarks[addProp] = temp;
                                    }
                                }

                            }
                        }
                        if (act.Observe != null)
                        {
                            foreach (GroundedPredicate addProp in act.HashObserve)
                            {
                                GroundedPredicate a1 = new GroundedPredicate(addProp);
                                GroundedPredicate a2 = new GroundedPredicate(addProp);
                                a2.Negation = !(a2.Negation);

                                if (!copyState.ContainsGroundedPredicate(a1))
                                {

                                    List<GroundedPredicate> temp = new List<GroundedPredicate>();
                                    temp.Add(a1);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        temp.Add(groundedGroundedPredicate);
                                    }

                                    allGroundedPredicateWithIsLandmarks.Add(a1, temp);
                                    copyState.AddGroundedPredicateWithoutcheck(a1);
                                    //StateGroundedPredicates.Add(a1);
                                    //tempList.Add(a1);
                                    //flag2 = true;
                                }
                                else
                                {
                                    List<GroundedPredicate> allPreFact = new List<GroundedPredicate>();
                                    List<GroundedPredicate> temp = new List<GroundedPredicate>();
                                    temp.Add(a1);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        allPreFact.AddRange(allGroundedPredicateWithIsLandmarks[groundedGroundedPredicate]);
                                    }
                                    if (!allPreFact.Contains(a1))
                                    {
                                        foreach (GroundedPredicate groundedGroundedPredicate in allGroundedPredicateWithIsLandmarks[a1])
                                        {
                                            if (allPreFact.Contains(groundedGroundedPredicate))
                                            {
                                                temp.Add(groundedGroundedPredicate);
                                            }
                                        }
                                        allGroundedPredicateWithIsLandmarks[a1] = temp;
                                    }
                                }


                                if (!copyState.ContainsGroundedPredicate(a2))
                                {

                                    List<GroundedPredicate> temp = new List<GroundedPredicate>();
                                    temp.Add(a2);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        temp.Add(groundedGroundedPredicate);
                                    }

                                    allGroundedPredicateWithIsLandmarks.Add(a2, temp);
                                    copyState.AddGroundedPredicateWithoutcheck(a2);
                                    //StateGroundedPredicates.Add(a2);
                                    //tempList.Add(a2);
                                    //flag2 = true;
                                }
                                else
                                {
                                    List<GroundedPredicate> allPreFact = new List<GroundedPredicate>();
                                    List<GroundedPredicate> temp = new List<GroundedPredicate>();
                                    temp.Add(a2);
                                    foreach (GroundedPredicate groundedGroundedPredicate in act.HashPrecondition)
                                    {
                                        allPreFact.AddRange(allGroundedPredicateWithIsLandmarks[groundedGroundedPredicate]);
                                    }
                                    if (!allPreFact.Contains(a2))
                                    {
                                        foreach (GroundedPredicate groundedGroundedPredicate in allGroundedPredicateWithIsLandmarks[a2])
                                        {
                                            if (allPreFact.Contains(groundedGroundedPredicate))
                                            {
                                                temp.Add(groundedGroundedPredicate);
                                            }
                                        }
                                        allGroundedPredicateWithIsLandmarks[a2] = temp;
                                    }
                                }
                            }
                        }
                    }


                }

                foreach (Action action in tempActionList)
                {
                    actions.Remove(action);
                    
                   
                }


            }
        }//NEED FIXING */


        
       
 
        protected bool IsMutuallyExclusive(GroundedPredicate s1,GroundedPredicate s2)
        {
            if (s1.Equals(s2.Negate())) return true;
                
                /*
                if (s1.Name == s2.Name && (!equalsContant) && s1.Negation == s2.Negation && s1.Negation == false)
                {
                    return true;
                }
                */
                return false;
            }
            

        
        public bool  Equals(Action a1,Action a2)
        {
            
                if (a1.Name == a2.Name && a1.Preconditions == null && a2.Preconditions == null)
                    return true;

                if (a1.Preconditions != null && a2.Preconditions != null)
                    if (a1.Name == a2.Name && a1.Preconditions.Equals(a2.Preconditions) )
                    {
                        return true;
                    }
                
            return false;
        }
        private bool Contains(HashSet<GroundedPredicate> x, HashSet<GroundedPredicate> y)
        {
             foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
        private bool Contains(HashSet<GroundedPredicate> x, HashSet<Predicate> y)
        {
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
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
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
       
        private bool Contains2(List<GroundedPredicate> x, List<GroundedPredicate> y)
        {
            HashSet<GroundedPredicate> tmp1 = new HashSet<GroundedPredicate>();
            HashSet<GroundedPredicate> tmp2 = new HashSet<GroundedPredicate>();
            List<GroundedPredicate> x1 = new List<GroundedPredicate>();
            List<GroundedPredicate> y1 = new List<GroundedPredicate>();
            foreach (GroundedPredicate gp in x)
            {
                tmp1.Add(gp);
               // x1.Add(gp);

            }
            foreach (GroundedPredicate gp in y)
            {
                tmp2.Add(gp);
                //y1.Add(gp);

            }
            return(Contains(tmp1,y) && Contains(tmp2,x));

        }

        public void FindPublicAndPrivateAction(out List<Action> publicAction, out List<Action> privateAction)
        {
            publicAction = new List<Action>();
            privateAction = new List<Action>();
            agentActionl = new Dictionary<string, List<Action>>();
            foreach (Action act in groundedAction)
            {
                if(!agentActionl.ContainsKey(act.agent))
                {
                    agentActionl.Add(act.agent, new List<Action>());
                    agentActionl[act.agent].Add(act);
                }
                else
                    agentActionl[act.agent].Add(act);
            }
            numberOfAgent = agentActionl.Count;
            agentActions = agentActionl;
            foreach (var pair in agentActionl)
            {
                foreach(Action act1 in pair.Value)
                {

                    foreach (var pair2 in agentActionl)
                    {
                        if (pair2.Key != pair.Key)
                        {
                            foreach (Action act2 in pair2.Value)
                            {
                                bool publicFlag=false;
                                foreach (GroundedPredicate eff in act1.HashEffects)
                                {
                                    if (act2.HashPrecondition.Contains(eff))
                                    {
                                        publicFlag = true;
                                        continue;
                                    }
                                }
                                if (!publicFlag)
                                {
                                        foreach (GroundedPredicate dell in act1.HashEffects)
                                        {
                                            if (act2.HashPrecondition.Contains(dell))
                                            {
                                                publicFlag = true;
                                                continue;
                                            }
                                        }
                                 }
                                if(publicFlag)
                                {

                                    if(!publicAction.Contains(act1))
                                        publicAction.Add(act1);
                                    if (!publicAction.Contains(act2))
                                        publicAction.Add(act2);
                                }
                                }
                            }
                        }
                    }
                }


            foreach (Action act in groundedAction)
            {
                if (!publicAction.Contains(act))
                {
                    privateAction.Add(act);
                }
            }

        }
        public HashSet<MutuallyExclusiveFacts> FindDTG()
        {

            // Dictionary<GroundedPredicate, List<GroundedPredicate>> temp = new Dictionary<GroundedPredicate, List<GroundedPredicate>>();
            Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> temp3 = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> temp4 = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            // Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> temp6 = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> temp2 = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            HashSet<MutuallyExclusiveFacts> mutuallyExclusive = new HashSet<MutuallyExclusiveFacts>();
            HashSet<MutuallyExclusiveFacts> mutuallyExclusive2 = new HashSet<MutuallyExclusiveFacts>();

            foreach (GroundedPredicate prop in allFactsWithActAchieve.Keys)
            {
                //temp.Add(prop, new List<GroundedPredicate>());
                temp2.Add(prop, new HashSet<GroundedPredicate>());
                temp3.Add(prop, new HashSet<GroundedPredicate>());
                temp4.Add(prop, new HashSet<GroundedPredicate>());
                // temp6.Add(prop, new HashSet<GroundedPredicate>());
                //mutuallyExclusive.Add(prop, new GroundedPredicate());
            }

            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp3)
            {
                foreach (Action act in allFactsWithActAchieve[iter.Key])
                {
                    foreach (GroundedPredicate add in act.HashEffects)
                    {
                        if (!add.Equals(iter.Key))
                        {
                            // temp[iter.Key].Add(add);
                            // temp6[iter.Key].Add(add);
                            temp3[iter.Key].Add(add);
                        }
                    }
                }
            }


            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp3)
            {
                if (allFactsWitTheirEffect.ContainsKey(iter.Key))
                {
                    foreach (GroundedPredicate prop in allFactsWitTheirEffect[iter.Key])
                    {
                        bool flag = false;
                        foreach (Action act in allFactsWithActAchieve[prop])
                        {
                            if (act.HashPrecondition.Contains(iter.Key) && !act.HashEffects.Contains(iter.Key.Negate()))
                            {
                                flag = true;
                                break;
                            }


                        }
                        if (flag)
                        {
                            if (!temp3[iter.Key].Contains(prop))
                            {
                                //temp[iter.Key].Add(prop);
                                temp3[iter.Key].Add(prop);
                                // temp6[iter.Key].Add(prop);
                            }
                        }

                    }
                }
            }

            bool again = true;






            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp2)
            {
                //temp2.Add(iter.Key,new List<GroundedPredicate>());
                if (allFactsWitTheirEffect.ContainsKey(iter.Key))
                {
                    foreach (GroundedPredicate prop in allFactsWitTheirEffect[iter.Key])
                    {
                        bool flag = true;
                        foreach (Action act in allFactsWithActAchieve[prop])
                        {
                            if (act.HashPrecondition.Contains(iter.Key) && !act.HashEffects.Contains(iter.Key.Negate()))
                            {
                                flag = false;
                                break;
                            }

                        }

                        if (flag)
                        {

                            if (!temp2[iter.Key].Contains(prop))
                                temp2[iter.Key].Add(prop);
                        }

                    }
                }

            }


            /*
                        foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp4)
                        {
                            bool con = true;
                            List<Action> listAction = new List<Action>();

                            listAction.AddRange(groundedAction);

                             List<GroundedPredicate> fixCopy = new List<GroundedPredicate>();
              
                                 //List<Action> removeListAction = new List<Action>();
                                 foreach (Action act in listAction)
                                 {
                                     if (act.Preconditions.Contains(iter.Key))
                                     {
                                         fixCopy.AddRange(act.AddList);
                                         //removeListAction.Add(act);
                                     }

                                 }
                                    
                            foreach (GroundedPredicate copyProp in fixCopy)
                            {
                                if (!iter.Key.Equals(copyProp) && !temp4[iter.Key].Contains(copyProp))
                                {
                                    con = true;
                                    temp4[iter.Key].Add(copyProp);
                                }
                            }

                           while (con)
                            {
                                con = false;
                                List <GroundedPredicate> copy = new List<GroundedPredicate>();
                                //List<GroundedPredicate> fixCopy = new List<GroundedPredicate>();
                                foreach (GroundedPredicate prop in iter.Value)
                                {
                                    List<Action> removeListAction = new List<Action>();
                                    foreach (Action act in listAction)
                                    {
                                        if (act.Preconditions.Contains(prop))
                                        {
                                                copy.AddRange(act.AddList);
                                                removeListAction.Add(act);                                
                                        }    
                                    }
                                    foreach (Action dell in removeListAction)
                                    {
                                        listAction.Remove(dell);
                                    }
                                }
                                foreach (GroundedPredicate copyProp in copy)
                                {
                                    if (!iter.Key.Equals(copyProp) && !temp4[iter.Key].Contains(copyProp))
                                    {
                                        con = true;
                                        temp4[iter.Key].Add(copyProp);
                                    }
                                }


                            }
                
                        }
                        */


            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp4)
            {
                if (allFactsWitTheirEffect.ContainsKey(iter.Key))
                {
                    foreach (GroundedPredicate copyProp in allFactsWitTheirEffect[iter.Key])
                    {
                        if (!temp4[iter.Key].Contains(copyProp))
                        {

                            temp4[iter.Key].Add(copyProp);
                        }
                    }
                }
            }






            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp4)
            {
                Queue<GroundedPredicate> q = new Queue<GroundedPredicate>();
                foreach (GroundedPredicate fact in iter.Value)
                {
                    q.Enqueue(fact);
                }
                while (q.Count != 0)
                {
                    GroundedPredicate fact = q.Dequeue();

                    foreach (GroundedPredicate prop in temp4[fact])
                    {
                        if (!iter.Key.Equals(prop) && !iter.Value.Contains(prop))
                        {
                            temp4[iter.Key].Add(prop);
                            q.Enqueue(prop);
                        }
                    }



                }
            }







            //*
            /*
            while(again)
            {
                again=false;
            foreach (KeyValuePair<GroundedPredicate, List<GroundedPredicate>> iter in temp)
            {
                List<GroundedPredicate> copy = new List<GroundedPredicate>();
                foreach(GroundedPredicate prop in temp[iter.Key])
                {
                    foreach (GroundedPredicate nextProp in temp[prop])
                    {

                        if (!temp[iter.Key].Contains(nextProp)&&!copy.Contains(nextProp))
                        {
                            copy.Add(nextProp);

                            //temp[iter.Key].Add(nextProp);
                            again = true;

                        }
                    }
                }
                foreach (GroundedPredicate fact in copy)
                {
                    temp[iter.Key].Add(fact);
                }
            }

           }
             * */







            ///
            /*
            while (again)
            {
                again = false;

                foreach (KeyValuePair<GroundedPredicate, List<GroundedPredicate>> iter in temp)
                {
                    List<GroundedPredicate> copylist = new List<GroundedPredicate>();
                    foreach (GroundedPredicate prop in temp[iter.Key])
                    {
                        foreach (GroundedPredicate nextProp in temp[prop])
                        {

                            if (!temp[iter.Key].Contains(nextProp) && !temp2[iter.Key].Contains(nextProp) && !copylist.Contains(nextProp))
                            {
                                copylist.Add(nextProp);
                                //temp[iter.Key].Add(nextProp);
                                again = true;

                            }
                        }
                    }
                    foreach (GroundedPredicate prop in copylist)
                    {
                        temp[iter.Key].Add(prop);
                        //temp3[iter.Key].Add(prop);
                    }
                }
            }
            
         ///
            */









            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp3)
            {
                Queue<GroundedPredicate> q = new Queue<GroundedPredicate>();
                foreach (GroundedPredicate fact in iter.Value)
                {
                    q.Enqueue(fact);
                }
                while (q.Count != 0)
                {
                    GroundedPredicate fact = q.Dequeue();
                    if(allFactsWitTheirEffect.ContainsKey(fact))
                    foreach (GroundedPredicate prop in allFactsWitTheirEffect[fact])
                    {
                        if (!temp2[iter.Key].Contains(prop) && !iter.Key.Equals(prop) && !iter.Value.Contains(prop))
                        {
                            temp3[iter.Key].Add(prop);
                            q.Enqueue(prop);
                        }
                    }



                }
            }












            /*




            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> iter in temp3)
            {
                bool con = true;
                List<Action> listAction = new List<Action>();

                listAction.AddRange(groundedAction);
                while (con)
                {
                    con = false;
                    List<GroundedPredicate> copy = new List<GroundedPredicate>();
                    foreach (GroundedPredicate prop in iter.Value)
                    {
                        List<Action> removeListAction = new List<Action>();
                        foreach (Action act in listAction)
                        {
                            if (act.Preconditions.Contains(prop))
                            {

                                if (!act.RemoveList.Contains(iter.Key))
                                {
                                    foreach (GroundedPredicate fact in act.AddList)
                                    {
                                        if (!temp2[iter.Key].Contains(fact))
                                        {
                                            copy.Add(fact);
                                            
                                        }
                                    }
                                    
                                }
                                removeListAction.Add(act);
                            }
                            
                        }
                        foreach (Action dell in removeListAction)
                        {
                            listAction.Remove(dell);
                        }
                    }
                    foreach (GroundedPredicate copyProp in copy)
                    {
                        if (!iter.Key.Equals(copyProp) && !temp3[iter.Key].Contains(copyProp))
                        {
                            con = true;
                            temp3[iter.Key].Add(copyProp);
                        }
                    }


                }

            }
            */
            /*
                        again = true;

                        while (again)
                        {
                            again = false;

                            foreach (KeyValuePair<GroundedPredicate, List<GroundedPredicate>> iter in temp2)
                            {
                                List<GroundedPredicate> copylist = new List<GroundedPredicate>();
                                foreach (GroundedPredicate prop in temp2[iter.Key])
                                {
                                    foreach (GroundedPredicate nextProp in temp2[prop])
                                    {

                                        if ( !temp2[iter.Key].Contains(nextProp) && !copylist.Contains(nextProp))
                                        {
                                            copylist.Add(nextProp);
                                            //temp[iter.Key].Add(nextProp);
                                            again = true;

                                        }
                                    }
                                }
                                foreach (GroundedPredicate prop in copylist)
                                {
                                    temp2[iter.Key].Add(prop);
                                }
                            }
                        }


                        */





            foreach (GroundedPredicate prop in allFactsWithActAchieve.Keys)
            {
                foreach (GroundedPredicate iter in allFactsWithActAchieve.Keys)
                {
                    //int da = 0;
                    /* if(!prop.Equals(iter))
                     {
                         if (!temp[prop].Contains(iter) && !temp[iter].Contains(prop) && temp2[prop].Contains(iter) && temp2[iter].Contains(prop))
                         {
                             MutuallyExclusiveFacts tempVar=new MutuallyExclusiveFacts(prop,iter);

                             if (!mutuallyExclusive.Contains(tempVar))
                             {
                                 mutuallyExclusive.Add(tempVar);
                                 Console.WriteLine("1: "+prop.ToString() + "<-->" + iter.ToString());
                             }
                             else
                             {
                                 da=0;
                             }

                           
                         }



                     }
                     */
                    if (!prop.Equals(iter))
                    {
                        if (!temp3[prop].Contains(iter) && !temp3[iter].Contains(prop) && (temp4[prop].Contains(iter) && temp4[iter].Contains(prop)))
                        {// note: if there is one way for two fact is can be problamatic
                            MutuallyExclusiveFacts tempVar = new MutuallyExclusiveFacts(prop, iter);

                            if (!mutuallyExclusive.Contains(tempVar))
                            {
                                mutuallyExclusive.Add(tempVar);
                                //Console.WriteLine("2: " + prop.ToString() + "<-->" + iter.ToString());
                                // da=4;
                            }
                            else
                            {
                                int r = 6;
                            }

                        }
                        else
                            if (!temp3[prop].Contains(iter) && !temp3[iter].Contains(prop) && (temp4[prop].Contains(iter) || temp4[iter].Contains(prop)))
                            {
                                MutuallyExclusiveFacts tempVar = new MutuallyExclusiveFacts(prop, iter);

                                if (!mutuallyExclusive2.Contains(tempVar))
                                {
                                    mutuallyExclusive2.Add(tempVar);

                                }
                            }


                    }

                }
            }



            return mutuallyExclusive;
        }
        private void FillFactDictionaryII(out Dictionary<Predicate, List<Action>> facts,out Dictionary<Predicate, List<Predicate>> facts2)
        {
            facts2 = new Dictionary<Predicate, List<Predicate>>();
            facts = new Dictionary<Predicate, List<Action>>();
            foreach (GroundedPredicate prop in problam.Known)
            {
                List<Action> templist = new List<Action>();
                facts.Add(prop, templist);

            }
            foreach (Action act in groundedAction)
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

                if (facts2 != null)
                {
                    foreach (GroundedPredicate prop2 in act.HashPrecondition)
                    {
                        if (!facts2.ContainsKey(prop2))
                        {
                            List<Predicate> templist = new List<Predicate>();
                            templist.AddRange(act.HashEffects);
                            facts2.Add(prop2, templist);

                        }

                        else
                        {
                            facts2[prop2].AddRange(act.HashEffects);
                        }


                    }

                }
            }

            Dictionary<Predicate, List<Predicate>> tmp = new Dictionary<Predicate, List<Predicate>>();
            foreach (KeyValuePair<Predicate, List<Predicate>> po in facts2)
            {
                if (!facts.ContainsKey(po.Key))
                {
                    tmp.Add(po.Key, null);

                }

            }

            foreach (KeyValuePair<Predicate, List<Predicate>> po in tmp)
            {
                facts2.Remove(po.Key);
            }

        }
    }
}

    

