using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    static class Distributed_Landmarks_Detection
    {
        static List<Agent> agents = null;
        public static List<PrivacyPreservingLandmark> PrivacyPreservingLandmarks;
        public static List<PPOrder> necessaryPPOrders;
        public static void Reset(List<Agent> m_agents)
        {
            agents = m_agents;
            PrivacyPreservingLandmark.m_agents = new List<string>();
            foreach (Agent ag in agents)
            {
                PrivacyPreservingLandmark.m_agents.Add(ag.name);
            }
            necessaryPPOrders = new List<PPOrder>();

        }
        public static List<Agent> Landmarks_Detection(List<Agent> m_agents, bool full)
        {
            agents = m_agents;
            PrivacyPreservingLandmark.m_agents = new List<string>();
            foreach (Agent ag in agents)
            {
                PrivacyPreservingLandmark.m_agents.Add(ag.name);
            }

            necessaryPPOrders = new List<PPOrder>();
            PrivacyPreservingLandmarks = new List<PrivacyPreservingLandmark>();
            Queue<PrivacyPreservingLandmark> PrivacyPreservingQueue = new Queue<PrivacyPreservingLandmark>();



            foreach (Agent agent in agents)
            {
                //agent.FirstIteration();
                List<PrivacyPreservingLandmark> tmp = agent.FirstIteration();
                if (full)
                    agent.fullDetection();
                foreach (var item in tmp)
                {
                    if (!PrivacyPreservingLandmarks.Contains(item))
                    {
                        if (item.toDevelop)
                        {
                            PrivacyPreservingQueue.Enqueue(item);
                            PrivacyPreservingLandmarks.Add(item);
                        }

                        else
                        {
                            PrivacyPreservingQueue.Enqueue(item);
                            PrivacyPreservingLandmarks.Add(item);
                        }
                    }
                }
            }

            while (PrivacyPreservingQueue.Count > 0)
            {

                PrivacyPreservingLandmark ppLandmark = PrivacyPreservingQueue.Dequeue();
                foreach (Agent agent in agents)
                {
                    agent.Reset();
                }

                KeyValuePair<Landmark, string> ans = new KeyValuePair<Landmark, string>();

                foreach (Agent agent in agents)
                {
                    agent.SetLandmarkToExplorer(ppLandmark);

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

                List<Agent> relevantAgents = new List<Agent>();
               
                foreach (Agent agent in agents)
                {
                    List<Action> lAchievers = agent.CanGet();
                    if (lAchievers != null)
                    {
                        relevantAgents.Add(agent);
                        ppLandmark.SetAchievers(agent.name, lAchievers);
                    }
                    else
                    {
                        ppLandmark.SetAchievers(agent.name, lAchievers);
                       // ppLandmark.RemoveAgent(agent.name);
                    }

                }
                if (ppLandmark.ToString().Equals("Empty"))
                {
                    PrivacyPreservingLandmarks.Remove(ppLandmark);
                    continue;
                }
                ppLandmark.TellAboutPublic(agents);
                if (ppLandmark.toDevelop)
                {
                    if (relevantAgents.Count == 1)
                    {
                        List<PrivacyPreservingLandmark> newPPLandmarks = relevantAgents.ElementAt(0).DetectNewLandmarks();

                        foreach (PrivacyPreservingLandmark ppl in newPPLandmarks)
                        {
                            bool insert = true;
                            foreach (PrivacyPreservingLandmark ppl2 in PrivacyPreservingLandmarks)
                            {
                                string str = PrivacyPreservingLandmark.Comparer(ppl, ppl2);
                                if (str == "First")
                                {
                                    PrivacyPreservingLandmarks.Remove(ppl2);
                                    List<PPOrder> delOrders = new List<PPOrder>();
                                    foreach (PPOrder order in necessaryPPOrders)
                                    {
                                        if ((order.lendmark1.Equals(ppl2)) || (order.lendmark2.Equals(ppl2)))
                                        {
                                            delOrders.Add(order);
                                        }
                                    }
                                    foreach (PPOrder ppo in delOrders)
                                    {
                                        necessaryPPOrders.Remove(ppo);
                                    }
                                    break;
                                }
                                if (str == "Second")
                                {
                                    insert = false;
                                    break;
                                }
                                if (str == "Identical")
                                {
                                    insert = false;
                                    break;

                                    insert = false;
                                    PPOrder tmpNecessaryOrder = new PPOrder("greedy-necessary", ppl2, ppLandmark);
                                    necessaryPPOrders.Add(tmpNecessaryOrder);
                                    break;
                                }

                            }
                            if (insert)
                            {
                                PrivacyPreservingLandmarks.Add(ppl);
                                PrivacyPreservingQueue.Enqueue(ppl);
                                PPOrder necessaryOrder = new PPOrder("greedy-necessary", ppl, ppLandmark);
                                necessaryPPOrders.Add(necessaryOrder);
                            }
                        }

                    }
                    else
                    {
                        List<PrivacyPreservingLandmark> newPPLandmarks;
                        Dictionary<string, List<PrivacyPreservingLandmark>> propNameToLandmarks = new Dictionary<string, List<PrivacyPreservingLandmark>>();
                        foreach (Agent relevantAget in relevantAgents)
                        {
                            newPPLandmarks = relevantAget.DetectNewLandmarks();

                            foreach (PrivacyPreservingLandmark ppl in newPPLandmarks)
                            {
                                if (!propNameToLandmarks.ContainsKey(ppl.type))
                                    propNameToLandmarks.Add(ppl.type, new List<PrivacyPreservingLandmark>());
                                propNameToLandmarks[ppl.type].Add(ppl);
                            }
                        }
                        foreach (List<PrivacyPreservingLandmark> lppLandmarks in propNameToLandmarks.Values)
                        {
                            if (lppLandmarks.Count == relevantAgents.Count)
                            {
                                PrivacyPreservingLandmark tmpLandmark = PrivacyPreservingLandmark.MergeList(lppLandmarks);
                                bool insert = true;
                                foreach (PrivacyPreservingLandmark ppl2 in PrivacyPreservingLandmarks)
                                {
                                    string str = PrivacyPreservingLandmark.Comparer(tmpLandmark, ppl2);
                                    if (str == "First")
                                    {
                                        PrivacyPreservingLandmarks.Remove(ppl2);
                                        List<PPOrder> delOrders = new List<PPOrder>();
                                        foreach (PPOrder order in necessaryPPOrders)
                                        {
                                            if ((order.lendmark1.Equals(ppl2)) || (order.lendmark2.Equals(ppl2)))
                                            {
                                                delOrders.Add(order);
                                            }
                                        }
                                        foreach (PPOrder ppo in delOrders)
                                        {
                                            necessaryPPOrders.Remove(ppo);
                                        }
                                        break;
                                    }
                                    if (str == "Second")
                                    {
                                        insert = false;
                                        break;
                                    }
                                    if (str == "Identical")
                                    {
                                        insert = false;
                                        break;
                                        insert = false;
                                        PPOrder tmpNecessaryOrder = new PPOrder("greedy-necessary", ppl2, ppLandmark);
                                        necessaryPPOrders.Add(tmpNecessaryOrder);
                                        break;
                                    }

                                }
                                if (insert)
                                {
                                    PrivacyPreservingLandmarks.Add(tmpLandmark);
                                    PrivacyPreservingQueue.Enqueue(tmpLandmark);
                                    PPOrder necessaryOrder = new PPOrder("greedy-necessary", tmpLandmark, ppLandmark);
                                    necessaryPPOrders.Add(necessaryOrder);
                                }
                            }
                        }
                    }
                }
            }
            int count = 0;
            foreach (var ppl in PrivacyPreservingLandmarks)
            {
                ppl.SetIndex(count);
                count++;
            }
            //List<Order> allReasonableorders = new List<Order>();
            Dictionary<string, List<Order>> agentROrder = new Dictionary<string, List<Order>>();
            foreach (Agent agent in agents)
            {
                List<Landmark> lLandmarks = new List<Landmark>();
                List<Order> necessaryOrders = new List<Order>();
                Dictionary<int, Landmark> mapTable = new Dictionary<int, Landmark>();
                foreach (PrivacyPreservingLandmark ppLandmark in PrivacyPreservingLandmarks)
                {
                    Landmark l = ppLandmark.GetAgentLandmark(agent.name);
                    lLandmarks.Add(l);
                    mapTable.Add(l.index, l);
                }
                foreach (PPOrder order in necessaryPPOrders)
                {
                    if ((mapTable.ContainsKey(order.lendmark1.index)) && (mapTable.ContainsKey(order.lendmark2.index)))
                    {
                        Landmark l1 = mapTable[order.lendmark1.index];
                        Landmark l2 = mapTable[order.lendmark2.index];
                        Order newOrder = new Order("greedy-necessary", l1, l2);
                        necessaryOrders.Add(newOrder);
                    }
                }
                // PrivacyPreservingLandmarks.ElementAt(0).ToString();
                List<Order> ans = agent.FindReasonableOrdering(lLandmarks, necessaryOrders, agents);
                agentROrder.Add(agent.name, ans);
                /* foreach (Order o in ans)
                 {
                     if (!allReasonableorders.Contains(o))
                     {
                         allReasonableorders.Add(o);
                     }

                 }*/
            }
            Dictionary<int, PrivacyPreservingLandmark> mapPPlandmark = new Dictionary<int, PrivacyPreservingLandmark>();
            foreach (PrivacyPreservingLandmark ppLandmark in PrivacyPreservingLandmarks)
            {
                mapPPlandmark.Add(ppLandmark.index, ppLandmark);
            }
            Dictionary<string, List<Order>> newAgentROrder = new Dictionary<string, List<Order>>();
            foreach (Agent agent in agents)
            {
                List<Order> localOrder = new List<Order>(agentROrder[agent.name]);
                foreach (var item in agentROrder)
                {
                    if (item.Key.Equals(agent.name))
                        continue;
                    foreach (Order rOrder in item.Value)
                    {
                        if (!localOrder.Contains(rOrder))
                        {
                            PrivacyPreservingLandmark ppl = mapPPlandmark[rOrder.lendmark2.index];
                            if (!ppl.achieversAgents.Contains(agent.name))
                            {
                                localOrder.Add(rOrder);
                            }
                            else
                            {
                                //localOrder.Add(rOrder);
                                Console.WriteLine(".............chack..............");
                            }
                        }
                    }
                }
                List<Order> del = new List<Order>();
                foreach (Order o in localOrder)
                {
                    Order newOrder = new Order("Reasonable", o.lendmark2, o.lendmark1);
                    if (localOrder.Contains(newOrder))
                    {
                        del.Add(newOrder);
                        del.Add(o);
                    }
                }
                foreach (Order dellOrder in del)
                {
                    if (localOrder.Contains(dellOrder))
                    {
                        localOrder.Remove(dellOrder);
                    }
                }
                newAgentROrder.Add(agent.name, localOrder);
                //allReasonableorders = new List<Order>();
                //agent.SetReasonableOrdering(localOrder);
            }
            List<Order> allReasonableorders = new List<Order>();
            if (newAgentROrder.Count > 0)
            {
                List<Order> first = newAgentROrder.ElementAt(0).Value;
                foreach (Order o in first)
                {
                    bool isShare = true;
                    foreach (var item in newAgentROrder)
                    {
                        if (!item.Value.Contains(o))
                        {
                            isShare = false;
                            continue;
                        }
                    }
                    if (isShare)
                    {
                        allReasonableorders.Add(o);
                    }
                }
            }
            foreach (Agent agent in agents)
            {
                //allReasonableorders = new List<Order>();
                agent.SetReasonableOrdering(allReasonableorders);
            }
           
            return agents;

        }
        public static KeyValuePair<List<List<Action>>, List<Landmark>> GetPublicActionsLandmarks(GroundedPredicate goalFact, Agent courentAgent,out int localDepth,bool pos)
        {
            List<List<Action>> publicActionslandmarks = new List<List<Action>>();
            List<Landmark> publicLandmark = new List<Landmark>();
            Queue<Landmark> PrivacyPreservingQueue = new Queue<Landmark>();
            List<Landmark> tmpForTest = new List<Landmark>();
            List<Landmark> tmpForDepthTest = new List<Landmark>();


            Landmark l = new Landmark("pre", false);
            l.AddPrivateFact(goalFact, "pre");
            l.isPublic = false;
            PrivacyPreservingQueue.Enqueue(l);
            //publicLandmark.Add(l);
            if (courentAgent.PublicPredicates.Contains(goalFact))
            {
                throw new Exception("it is not should to be public predicate");
            }

            foreach (Agent agent in agents)
            {
                if (agent.name.Equals(courentAgent.name))
                    agent.initPublicLandmarksDetect(l);
                else
                    agent.initPublicLandmarksDetect(null);
            }

            List<Action> allAchievers;

            int index=0;
            while (PrivacyPreservingQueue.Count > 0)
            {
                bool closeLandmark = false;
                allAchievers = null;

                Landmark ppLandmark = PrivacyPreservingQueue.Dequeue();
                if (ppLandmark.facts.Count == 0)
                    Console.WriteLine("ddd");
                bool f = true;
                foreach (Landmark land in tmpForTest)
                {
                    if (land.Equals(ppLandmark))
                    {
                        f = false;
                        break;
                    }
                }
                if (f)
                {
                    Landmark nl = new Landmark("dd", false);
                    nl.facts = new Dictionary<GroundedPredicate, string>(ppLandmark.facts);
                    nl.index = ppLandmark.index;
                    tmpForTest.Add(nl);
                }

                foreach (Landmark land in tmpForDepthTest)
                {
                    if (land.Identical(ppLandmark))
                    {
                        f = false;
                        break;
                    }
                }
                if (f)
                {

                    tmpForDepthTest.Add(ppLandmark);
                }

                foreach (Agent agent in agents)
                {
                    agent.Reset();
                }




                foreach (Agent agent in agents)
                {
                    if (courentAgent.name.Equals(agent.name))
                    {
                        agent.SetLandmarkToExplorer(ppLandmark);
                    }
                    else
                    {
                        agent.SetLandmarkToExplorer((Landmark)null);
                    }
                }


                HashSet<GroundedPredicate> publicSet = new HashSet<GroundedPredicate>();

                foreach (Agent agent in agents)
                {
                    HashSet<GroundedPredicate> tmp = agent.DetectionGlobal();
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

                List<Agent> relevantAgents = new List<Agent>();

                foreach (Agent agent in agents)
                {
                    List<Action> lAchievers = agent.CanGet();

                    if (lAchievers != null)
                    {
                        relevantAgents.Add(agent);
                        allAchievers = lAchievers;
                        if (!ppLandmark.secondRound)
                        {
                            foreach (GroundedPredicate fact in ppLandmark.facts.Keys.ToList())
                            {
                                bool flag = false;
                                foreach (Action act in lAchievers)
                                {

                                    if (act.HashEffects.Contains(fact))
                                    {
                                        flag = true;
                                        break;
                                    }
                                }
                                if (!flag)
                                {
                                    ppLandmark.facts.Remove(fact);
                                }
                            }


                            List<Action> publicActions = courentAgent.GetPublicActions(lAchievers);
                            List<Action> privateAchievers = new List<Action>(allAchievers);
                            foreach (Action pubAct in publicActions)
                            {
                                privateAchievers.Remove(pubAct);
                            }
                            bool possibleInTheInitial = agent.PossibleInTheInitial(privateAchievers);
                            /* bool test = agent.PossibleInTheInitial(allAchievers);
                             if (test && !possibleInTheInitial)
                             {
                                 Console.WriteLine("***");
                             }*/
                            if (ppLandmark.AchieversPossibleInTheInitial == false)
                            {
                                ppLandmark.AchieversPossibleInTheInitial = possibleInTheInitial;
                            }
                            if (publicActions.Count > 0)
                            {
                                if (ppLandmark.lAchievers != null)
                                    ppLandmark.lAchievers.AddRange(publicActions);
                                else
                                    ppLandmark.lAchievers = publicActions;
                                if (publicActions.Count == lAchievers.Count)
                                {
                                    closeLandmark = true;
                                }
                            }
                        }
                    }

                }
                if (ppLandmark.lAchievers == null)
                    ppLandmark.lAchievers = new List<Action>();
                if (allAchievers == null)
                    ppLandmark.secondRound = true;
                if (!closeLandmark && ppLandmark.secondRound)
                {

                    if (relevantAgents.Count == 1)
                    {
                        List<Landmark> newPPLandmarks = relevantAgents.ElementAt(0).DetectNewLocalLandmarks(true);
                        foreach (Landmark slave in newPPLandmarks)
                        {                           
                            slave.myMuster = ppLandmark;
                            slave.index = index;
                            index++;
                        }
                        for (int i = 0; i < newPPLandmarks.Count; i++)
                        {
                            Landmark ppl = newPPLandmarks.ElementAt(i);
                            ppl.AchieversPossibleInTheInitial = ppLandmark.AchieversPossibleInTheInitial;
                            ppl.lAchievers = new List<Action>(ppLandmark.lAchievers);
                            PrivacyPreservingQueue.Enqueue(ppl);
                        }
                        if (newPPLandmarks.Count == 0)
                        {

                            if (ppLandmark.lAchievers != null && ppLandmark.lAchievers.Count > 0 )
                            {
                                if (ppLandmark.publicEffects != null)
                                {
                                    ppLandmark.facts = new Dictionary<GroundedPredicate, string>();
                                    foreach (GroundedPredicate gp in ppLandmark.publicEffects)
                                    {
                                        ppLandmark.facts.Add(gp, "pre");
                                    }
                                
                                publicLandmark.Add(ppLandmark);
                                }
                            }

                        }

                    }
                    else
                    {
                        if (relevantAgents.Count > 1)
                        {
                            throw new Exception("only one agent can Achieve private landmark");
                        }
                        if (relevantAgents.Count == 0)
                        {
                            if (ppLandmark.lAchievers != null && ppLandmark.lAchievers.Count > 0)
                            {
                                ppLandmark.facts = new Dictionary<GroundedPredicate, string>();
                                foreach (GroundedPredicate gp in ppLandmark.publicEffects)
                                {
                                    ppLandmark.facts.Add(gp, "pre");
                                }
                                publicLandmark.Add(ppLandmark);
                            }
                        }
                    }
                }
                else
                {
                    if (closeLandmark)
                    {
                        publicLandmark.Add(ppLandmark);
                    }
                    else
                    {

                        foreach (GroundedPredicate gp in ppLandmark.facts.Keys.ToList())
                        {
                            bool dell = true;
                            foreach (Action act in allAchievers)
                            {
                                if (ppLandmark.lAchievers == null || !ppLandmark.lAchievers.Contains(act))
                                {
                                    if (act.HashEffects.Contains(gp))
                                    {
                                        dell = false;
                                        break;
                                    }
                                }
                            }

                            if (dell)
                            {
                                if (ppLandmark.publicEffects == null)
                                    ppLandmark.publicEffects = new List<GroundedPredicate>();
                                ppLandmark.publicEffects.Add(gp);
                                ppLandmark.facts.Remove(gp);
                            }
                            else
                            {
                                bool flag = false;
                                if (ppLandmark.lAchievers != null)
                                {
                                    foreach (Action act in ppLandmark.lAchievers)
                                    {
                                        if (act.HashEffects.Contains(gp))
                                        {
                                            flag = true;
                                            break;
                                        }
                                    }
                                    if (flag)
                                    {
                                        if (ppLandmark.publicEffects == null)
                                            ppLandmark.publicEffects = new List<GroundedPredicate>();
                                        ppLandmark.publicEffects.Add(gp);
                                    }
                                }
                            }
                        }
                        ppLandmark.secondRound = true;
                        PrivacyPreservingQueue.Enqueue(ppLandmark);
                    }
                }

            }
            if (pos)
            {
                int size = 0;
                foreach (Landmark la in tmpForTest)
                {
                    size += la.facts.Count();
                }
                    Program.sizeOfRegressionTree+= size;
            }
                HashSet<Landmark> dellPar = new HashSet<Landmark>();
                foreach (Landmark land in tmpForDepthTest)
                {
                    if (land.myMuster != null)
                        dellPar.Add(land.myMuster);
                }
                foreach (Landmark ldel in dellPar)
                {
                    tmpForDepthTest.Remove(ldel);
                }
                int depth = 0;
                foreach (Landmark land in tmpForDepthTest)
                {
                    depth += land.depth;
                }
                localDepth = depth;
            List<Landmark> landmarks = new List<Landmark>();
            for (int i = 0; i < publicLandmark.Count; i++)
            {
                Landmark ppl = publicLandmark.ElementAt(i);
                if (ppl.lAchievers != null)
                {
                    landmarks.Add(ppl);
                    publicActionslandmarks.Add(ppl.lAchievers);
                }
            }


            return new KeyValuePair<List<List<Action>>, List<Landmark>>(publicActionslandmarks, landmarks); ;

        }

        public static HashSet<Action> GetPublicActionsLandmarks2(GroundedPredicate goalFact, Agent courentAgent,out int dept, bool pos)
        {
            dept = 0;
            string gpName = goalFact.Name + " " + goalFact.Constants[0];
            List<Landmark> lowLayerLandmarks = new List<Landmark>();
            if (courentAgent.PublicPredicates.Contains(goalFact))
                throw new Exception();
            Landmark firstLandmark = new Landmark("firstFact",false);
            firstLandmark.lAchievers = new List<Action>();
            firstLandmark.facts.Add(goalFact, "fact");
            Queue<Landmark> queue = new Queue<Landmark>();
            queue.Enqueue(firstLandmark);
            HashSet<GroundedPredicate> usedFacts = new HashSet<GroundedPredicate>();
            usedFacts.Add(goalFact);
            while (queue.Count>0)
            {
                Landmark courrentLandmark = queue.Dequeue();
                HashSet<Action> CanAchiveList = CanAchive(courrentLandmark,courentAgent);
                List<Action> privateSet = new List<Action>();
                List<Action> PublicSet = new List<Action>();
                foreach(Action act in CanAchiveList)
                {
                    if(act.isPublic)
                    {
                        PublicSet.Add(act);
                    }
                    else
                    {
                        privateSet.Add(act);
                    }
                }
                courrentLandmark.lAchievers.AddRange(PublicSet);
                //privateSet = courentAgent.GetUnPosibalePrivateAction(privateSet);
                List<Landmark> newsPPLandmarks = DetectNewLandmarks(privateSet, usedFacts);
                List<Landmark> tmp = new List<Landmark>();

                foreach(Landmark l in newsPPLandmarks)
                {
                    Landmark newLand = new Landmark(l.type, l.GoalLandmark);
                    foreach(var itemFact in l.facts)
                    {
                        string factName = itemFact.Key.Name + " " + itemFact.Key.Constants[0];
                        if(factName.Equals(gpName))
                        {
                            newLand.AddFact(itemFact.Key, itemFact.Value);
                        }
                    }
                    if (newLand.facts.Count > 0)
                        tmp.Add(newLand);
                }
                newsPPLandmarks = tmp;
                if (newsPPLandmarks.Count > 0)
                {
                    foreach (Landmark l in newsPPLandmarks)
                    {
                        l.lAchievers = new List<Action>();
                        l.lAchievers.AddRange(courrentLandmark.lAchievers);
                        queue.Enqueue(l);
                    }
                }
                else
                {
                    lowLayerLandmarks.Add(courrentLandmark);
                }
                
            }
            // List<List<Action>> achievers = new List<List<Action>>();
            //achievers.Add(new List<Action>());

            HashSet<Action> achievers = new HashSet<Action>();
            foreach (Landmark l in lowLayerLandmarks)
            {
                foreach(Action act in l.lAchievers)
                {
                    achievers.Add(act);
                }
                /* if(l.lAchievers.Count>0)
                 {
                     if(achievers.Count==0)
                     {
                         foreach (Action act in l.lAchievers)
                         {
                             achievers.Add(act);
                         }
                     }
                     else
                     {
                         HashSet<Action> tmp = new HashSet<Action>();
                         foreach(Action act in l.lAchievers)
                         {
                             if (achievers.Contains(act))
                                 tmp.Add(act);
                         }
                         achievers = tmp;
                     }
                 }*/
            }
            return  achievers;
        }
        public static HashSet<Action> CanAchive(Landmark l,Agent agent)
        {
            HashSet<Action> CanAchiveList = new HashSet<Action>();
            foreach(GroundedPredicate gp in l.facts.Keys)
            {
                foreach(Action act in agent.m_actions)
                {
                    if(act.HashEffects.Contains(gp))
                    {
                        CanAchiveList.Add(act);
                    }
                }
            }
            return CanAchiveList;

        }
        public static List<Landmark> DetectNewLandmarks(List<Action> PossibleBefore, HashSet<GroundedPredicate> usedFacts)
        {
            int indexProp = 1;
            List<Landmark> newsPPLandmarks = new List<Landmark>();
            bool flag2 = false;
            if (PossibleBefore.Count > 0)
            {
                HashSet<GroundedPredicate> oldFacts = new HashSet<GroundedPredicate>();
                Action firstAction = PossibleBefore[0];
                foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                {
                    if (usedFacts.Contains(prop))
                        continue;
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
                        Landmark newLandmark = new Landmark("fact", false);
                        newLandmark.AddFact(prop, "first_round");
                        indexProp++;
                        newsPPLandmarks.Add(newLandmark);
                        oldFacts.Add(prop);
                        usedFacts.Add(prop);
                    }
                }
                if (PossibleBefore.Count > 1)
                    firstAction = PossibleBefore[0];
                PossibleBefore.RemoveAt(0);

                foreach (GroundedPredicate prop in firstAction.HashPrecondition)
                {
                    string type = prop.Name;
                    //  if (!oldFacts.Contains(prop) && !usedFacts.Contains(prop))
                    {
                        int counter = 0; ;
                        Landmark newLandmark = new Landmark("Disjunctive", false);
                        //newLandmark.worth = exploreLandmarks.worth - 10;
                        if (oldFacts.Contains(prop))
                            continue;
                        if (!usedFacts.Contains(prop))
                        {
                            newLandmark.AddFact(prop, "first_round");
                        }
                        foreach (Action act in PossibleBefore)
                        {
                            bool f = false;
                            foreach (GroundedPredicate prop2 in act.HashPrecondition)
                            {
                                if (prop2.Name == prop.Name)
                                {

                                    if (!newLandmark.facts.ContainsKey(prop2) && !usedFacts.Contains(prop2))
                                    {
                                        newLandmark.AddFact(prop2, "first_round");
                                    }
                                    counter++;
                                    f = true;
                                    break;
                                }
                            }
                        }
                        if (counter == PossibleBefore.Count && newLandmark.facts.Count > 0)
                        {
                            newsPPLandmarks.Add(newLandmark);
                            foreach(GroundedPredicate gp in newLandmark.facts.Keys)
                            {
                                usedFacts.Add(gp);
                            }
                        }
                    }
                }
            }

            return newsPPLandmarks;
        }

        public static List<Landmark> GetPublicLandmarks(GroundedPredicate goalFact, Agent courentAgent)
        {



            List<List<Action>> publicActionslandmarks = new List<List<Action>>();
            List<Landmark> publicLandmark = new List<Landmark>();
            Queue<Landmark> PrivacyPreservingQueue = new Queue<Landmark>();




            Landmark l = new Landmark("pre", false);
            l.AddPrivateFact(goalFact, "pre");
            l.isPublic = false;
            PrivacyPreservingQueue.Enqueue(l);
            // publicLandmark.Add(l);


            if (courentAgent.PublicPredicates.Contains(goalFact))
            {
                throw new Exception("it is not should to be public predicate");
            }

            foreach (Agent agent in agents)
            {
                if (agent.name.Equals(courentAgent.name))
                    agent.initPublicLandmarksDetect(l);
                else
                    agent.initPublicLandmarksDetect(null);
            }






            while (PrivacyPreservingQueue.Count > 0)
            {

                Landmark ppLandmark = PrivacyPreservingQueue.Dequeue();

                foreach (Agent agent in agents)
                {
                    agent.Reset();
                }



                foreach (Agent agent in agents)
                {
                    if (courentAgent.name.Equals(agent.name))
                    {
                        agent.SetLandmarkToExplorer(ppLandmark);
                    }
                    else
                    {
                        agent.SetLandmarkToExplorer((Landmark)null);
                    }
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

                List<Agent> relevantAgents = new List<Agent>();

                foreach (Agent agent in agents)
                {
                    List<Action> lAchievers = agent.CanGet();
                    if (lAchievers != null)
                    {
                        relevantAgents.Add(agent);
                        List<Action> publicActions = courentAgent.GetPublicActions(lAchievers);
                        if (publicActions.Count > 0)
                        {
                            if (ppLandmark.lAchievers != null)
                                ppLandmark.lAchievers.AddRange(publicActions);
                            else
                                ppLandmark.lAchievers = publicActions;
                        }
                    }

                }


                if (relevantAgents.Count == 1)
                {
                    List<Landmark> newPPLandmarks = relevantAgents.ElementAt(0).DetectNewLocalLandmarks(false);

                    for (int i = 0; i < newPPLandmarks.Count; i++)
                    {
                        Landmark ppl = newPPLandmarks.ElementAt(i);
                        if (ppLandmark.mix)
                        {
                            publicLandmark.Remove(ppLandmark);
                            List<GroundedPredicate> publicFacts = courentAgent.GetPublicFacts(ppLandmark.facts.Keys.ToList());
                            foreach (GroundedPredicate publicFact in publicFacts)
                            {
                                ppl.AddPublicFact(publicFact, "pre");
                            }
                            ppl.lAchievers = new List<Action>();
                            ppl.lAchievers.AddRange(ppLandmark.lAchievers);
                        }

                        if (ppl.isPublic || ppl.mix)
                        {
                            publicLandmark.Add(ppl);
                        }
                        if (!ppl.isPublic || ppl.mix)
                        {
                            PrivacyPreservingQueue.Enqueue(ppl);
                        }
                    }

                }
                else
                {
                    if (relevantAgents.Count > 1)
                        throw new Exception("only one agent can Achieve private landmark");
                }

            }
            List<Landmark> ans = new List<Landmark>();
            for (int i = 0; i < publicLandmark.Count; i++)
            {
                Landmark ppl = publicLandmark.ElementAt(i);
                Landmark newl = new Landmark("Goal", true);
                foreach (GroundedPredicate pgp in courentAgent.GetPublicFacts(ppl.facts.Keys.ToList()))
                {
                    newl.AddPublicFact(pgp, "art-goal");
                }
                ans.Add(newl);
            }


            return ans;

        }
    }
}
