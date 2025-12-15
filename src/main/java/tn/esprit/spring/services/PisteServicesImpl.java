package tn.esprit.spring.services;

import java.util.List;

import org.springframework.stereotype.Service;

import lombok.AllArgsConstructor;
import tn.esprit.spring.entities.Piste;
import tn.esprit.spring.repositories.IPisteRepository;
@AllArgsConstructor
@Service
public class PisteServicesImpl implements  IPisteServices{

    private IPisteRepository pisteRepository;

        /*@ ensures \result != null; @*/
    @Override
    public List<Piste> retrieveAllPistes() {
        return pisteRepository.findAll();
    }

    /*@ requires piste != null;
      @ ensures \result != null;
      @*/
    @Override
    public Piste addPiste(Piste piste) {
        return pisteRepository.save(piste);
    }

    /*@ requires numPiste != null;
      @ ensures true;
      @*/
    @Override
    public void removePiste(Long numPiste) {
        pisteRepository.deleteById(numPiste);
    }

    /*@ requires numPiste != null;
      @ ensures true; // may return null if not found
      @*/
    @Override
    public Piste retrievePiste(Long numPiste) {
        return pisteRepository.findById(numPiste).orElse(null);
    }

}
