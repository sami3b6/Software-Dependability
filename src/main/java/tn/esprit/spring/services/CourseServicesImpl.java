package tn.esprit.spring.services;

import java.util.List;

import org.springframework.stereotype.Service;

import lombok.AllArgsConstructor;
import tn.esprit.spring.entities.Course;
import tn.esprit.spring.repositories.ICourseRepository;
@AllArgsConstructor
@Service


public class CourseServicesImpl implements  ICourseServices{

    private ICourseRepository courseRepository;

        /*@ ensures \result != null; @*/
    @Override
    public List<Course> retrieveAllCourses() {
        return courseRepository.findAll();
    }

    /*@ requires course != null;
      @ ensures \result != null;
      @*/
    @Override
    public Course addCourse(Course course) {
        return courseRepository.save(course);
    }

    /*@ requires course != null;
      @ ensures \result != null;
      @*/
    @Override
    public Course updateCourse(Course course) {
        return courseRepository.save(course);
    }

    /*@ requires numCourse != null;
      @ ensures true;  // may return null if not found
      @*/
    @Override
    public Course retrieveCourse(Long numCourse) {
        return courseRepository.findById(numCourse).orElse(null);
    }



}
