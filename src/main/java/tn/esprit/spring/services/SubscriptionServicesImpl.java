package tn.esprit.spring.services;

import java.time.LocalDate;
import java.util.List;
import java.util.Set;

import org.springframework.stereotype.Service;

import lombok.AllArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import tn.esprit.spring.entities.Subscription;
import tn.esprit.spring.entities.TypeSubscription;
import tn.esprit.spring.repositories.ISkierRepository;
import tn.esprit.spring.repositories.ISubscriptionRepository;

@Slf4j
@AllArgsConstructor
@Service
public class SubscriptionServicesImpl implements ISubscriptionServices {

    private ISubscriptionRepository subscriptionRepository;
    private ISkierRepository skierRepository;

    /*@
      @ requires type != null;
      @ requires start != null;
      @ ensures type == TypeSubscription.ANNUAL     ==> \result.equals(start.plusYears(1));
      @ ensures type == TypeSubscription.SEMESTRIEL ==> \result.equals(start.plusMonths(6));
      @ ensures type == TypeSubscription.MONTHLY    ==> \result.equals(start.plusMonths(1));
      @*/
    public static LocalDate computeEndDate(TypeSubscription type, LocalDate start) {
        switch (type) {
            case ANNUAL:
                return start.plusYears(1);
            case SEMESTRIEL:
                return start.plusMonths(6);
            case MONTHLY:
                return start.plusMonths(1);
            default:
                // unreachable if enum is only these values, but keeps Java happy
                return start;
        }
    }

    /*@
      @ requires subscription != null;
      @ requires subscription.getTypeSub() != null;
      @ requires subscription.getStartDate() != null;
      @ ensures subscription.getEndDate() != null;
      @ ensures subscription.getTypeSub() == TypeSubscription.ANNUAL
      @      ==> subscription.getEndDate().equals(subscription.getStartDate().plusYears(1));
      @ ensures subscription.getTypeSub() == TypeSubscription.SEMESTRIEL
      @      ==> subscription.getEndDate().equals(subscription.getStartDate().plusMonths(6));
      @ ensures subscription.getTypeSub() == TypeSubscription.MONTHLY
      @      ==> subscription.getEndDate().equals(subscription.getStartDate().plusMonths(1));
      @*/
    @Override
    public Subscription addSubscription(Subscription subscription) {
        subscription.setEndDate(computeEndDate(subscription.getTypeSub(), subscription.getStartDate()));
        return subscriptionRepository.save(subscription);
    }

    @Override
    public Subscription updateSubscription(Subscription subscription) {
        return subscriptionRepository.save(subscription);
    }

    @Override
    public Subscription retrieveSubscriptionById(Long numSubscription) {
        return subscriptionRepository.findById(numSubscription).orElse(null);
    }


   // @Scheduled(cron = "* 0 9 1 * *") /* Cron expression to run a job every month at 9am */
  //  @Scheduled(cron = "*/30 * * * * *") /* Cron expression to run a job every 30 secondes */
    public void showMonthlyRecurringRevenue() {
        Float revenue = subscriptionRepository.recurringRevenueByTypeSubEquals(TypeSubscription.MONTHLY)
                + subscriptionRepository.recurringRevenueByTypeSubEquals(TypeSubscription.SEMESTRIEL)/6
                + subscriptionRepository.recurringRevenueByTypeSubEquals(TypeSubscription.ANNUAL)/12;
        log.info("Monthly Revenue = " + revenue);
    }

    @Override
    public Set<Subscription> getSubscriptionByType(TypeSubscription type) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'getSubscriptionByType'");
    }

    @Override
    public List<Subscription> retrieveSubscriptionsByDates(LocalDate startDate, LocalDate endDate) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'retrieveSubscriptionsByDates'");
    }

    @Override
    public void retrieveSubscriptions() {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'retrieveSubscriptions'");
    }
}
