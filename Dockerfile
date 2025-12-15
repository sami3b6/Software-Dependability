# Java 11 runtime (matches your pom.xml)
FROM eclipse-temurin:11-jre

WORKDIR /app

# copy the built jar into the image
COPY target/gestion-station-ski-1.0.jar app.jar

EXPOSE 8080

ENTRYPOINT ["java","-jar","/app/app.jar"]
